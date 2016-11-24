/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ICAN",
    /* First member's full name */
    "杨森",
    /* First member's email address */
    "15302010025@fudan.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

//所以下面是宏定义的部分
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
//这里应该是定义了一个常数ALIGNMENT为8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
//这里定义了一个函数ALIGN
//这里实现了向8对齐,如果不足8,会补上相应部分,相应的,等于8,不会增加

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) //这里是按size_t的大小来分配
// sizey_t根据机器的不同而不同所以有很大的移植性
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define SET_P(bp, addr) (*(unsigned int *)(bp) = (unsigned int)(addr))
#define PREC_P(bp) ((char *)(bp))
#define SUCC_P(bp) ((char *)(bp) + WSIZE)

#define PREC(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_P(bp)))

#define MAXLIST 16

static char *heap_listp = 0;
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert(void *bp, size_t size);
static void delete (void *bp);

static void *lists[MAXLIST];

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
    return -1;
  }

  for (int list = 0; list < MAXLIST; list++) {
    lists[list] = NULL;
  }

  PUT(heap_listp, 0);
  PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
  PUT(heap_listp + DSIZE, PACK(DSIZE, 1));
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

  heap_listp += DSIZE;

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
    return -1;
  }
  return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
  int index = 0;

  size_t asize;
  size_t extendsize;
  char *bp = NULL;

  if (heap_listp == 0) {
    mm_init();
  }

  if (size == 0)
    return NULL;

  if (size <= DSIZE) {
    asize = 2 * DSIZE;
  } else {
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  size_t loopsize = asize;

  while (index < MAXLIST) {
    if ((index == MAXLIST - 1) || ((loopsize <= 1) && (lists[index] != NULL))) {
      bp = lists[index];

      while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))))) {
        bp = SUCC(bp);
      }
      if (bp != NULL)
        break;
    }

    loopsize >>= 1;
    index++;
  }

  if (bp != NULL) {
    bp = place(bp, asize);
    return bp;
  }

  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
    return NULL;
  }

  bp = place(bp, asize);

  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
  if (bp == 0)
    return;

  size_t size = GET_SIZE(HDRP(bp));

  if (heap_listp == 0) {
    mm_init();
  }

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  // insert(bp, size);
  coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

void *mm_realloc(void *bp, size_t size) {
  if (size < 0)
    return NULL;
  else if (size == 0) {
    mm_free(bp);
    return NULL;
  }

  size_t oldsize = GET_SIZE(HDRP(bp));
  size_t newsize = ALIGN(size + DSIZE);

  if (newsize <= oldsize) {
    return bp;
  } else {
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t csize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(bp)));

    //优化1 能不memcpy就不memcpy  在原有基础上扩展
    if (!next_alloc && csize >= newsize) {
      delete (NEXT_BLKP(bp));
      PUT(HDRP(bp), PACK(csize, 1));
      PUT(FTRP(bp), PACK(csize, 1));
      return bp;
    }
    //优化2 在末尾可以extend相应大小的size使得它不发生移动
    if (!GET_SIZE(HDRP(NEXT_BLKP(bp)))) {
      size_t extendsize = newsize - csize;

      if (extend_heap(extendsize / WSIZE) == NULL)
        return NULL;

      delete (NEXT_BLKP(bp));
      PUT(HDRP(bp), PACK(newsize, 1));
      PUT(FTRP(bp), PACK(newsize, 1));
      return bp;
    }
    void *new_ptr = mm_malloc(newsize);
    //这里不能place,place会对指针进行操作,cpy会出错
    memcpy(new_ptr, bp, newsize);
    mm_free(bp);
    return new_ptr;
  }
}

/***help function ----- we need to deal with some problems***/ //
static void *coalesce(void *bp) {
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  if (prev_alloc && next_alloc) {
    insert(bp, size);
    return bp;
  } else if (prev_alloc && !next_alloc) {
    void *next_bp = NEXT_BLKP(bp);

    delete (next_bp);

    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    void *prev_bp = PREV_BLKP(bp);

    delete (prev_bp);

    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = prev_bp;
  } else {
    void *next_bp = NEXT_BLKP(bp);
    void *prev_bp = PREV_BLKP(bp);

    delete (next_bp);
    delete (prev_bp);

    size = size + GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));

    bp = prev_bp;
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  insert(bp, size);

  return bp;
}

static void *extend_heap(size_t words) {

  char *bp;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

  if ((long)(bp = mem_sbrk(size)) == -1) {
    return NULL;
  }
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

  return coalesce(bp);
}

static void *place(void *bp, size_t asize) {
  delete (bp);
  size_t csize = GET_SIZE(HDRP(bp));

  //优化3 小块在前  大块在后 保持统一
  if ((csize - asize) < (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  } else if (asize >= 90) {
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    void *next_bp = NEXT_BLKP(bp);
    PUT(HDRP(next_bp), PACK(asize, 1));
    PUT(FTRP(next_bp), PACK(asize, 1));
    insert(bp, csize - asize);
    return next_bp;
  } else {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    void *next_bp = NEXT_BLKP(bp);
    PUT(HDRP(next_bp), PACK(csize - asize, 0));
    PUT(FTRP(next_bp), PACK(csize - asize, 0));
    insert(next_bp, csize - asize);
  }
  return bp;
}

/*****help function ------ lists*****/
// here is the function we can insert the node of lists
static void insert(void *bp, size_t size) {

  int index = 0;
  void *search_bp = NULL;
  void *insert_bp = NULL;

  size_t loopsize = size;
  while (index < (MAXLIST - 1) && loopsize > 1) {
    loopsize >>= 1;
    index++;
  }

  search_bp = lists[index];

  while ((search_bp != NULL) && size > GET_SIZE(HDRP(search_bp))) {
    insert_bp = search_bp;

    search_bp = SUCC(search_bp);
  }
  if (search_bp != NULL) {
    if (insert_bp != NULL) {
      SET_P(SUCC_P(bp), search_bp);
      SET_P(PREC_P(bp), insert_bp);
      SET_P(SUCC_P(insert_bp), bp);
      SET_P(PREC_P(search_bp), bp);
    } else {
      SET_P(SUCC_P(bp), search_bp);
      SET_P(PREC_P(bp), NULL);
      SET_P(PREC_P(search_bp), bp);
      lists[index] = bp;
    }
  } else {
    if (insert_bp != NULL) {
      SET_P(SUCC_P(bp), NULL);
      SET_P(PREC_P(bp), insert_bp);
      SET_P(SUCC_P(insert_bp), bp);
    } else {

      SET_P(PREC_P(bp), NULL);
      SET_P(SUCC_P(bp), NULL);
      lists[index] = bp;
    }
  }
  return;
}

// we also need to delte the node of lists
static void delete (void *bp) {
  if (bp == NULL) {
    return;
  }
  int index = 0;
  size_t size = GET_SIZE(HDRP(bp));

  void *prec_bp = PREC(bp);
  void *succ_bp = SUCC(bp);

  while (index < (MAXLIST - 1) && size > 1) {
    size >>= 1;
    index++;
  }

  if (prec_bp != NULL && succ_bp != NULL) {
    SET_P(SUCC_P(prec_bp), succ_bp);
    SET_P(PREC_P(succ_bp), prec_bp);
  } else if (prec_bp == NULL && succ_bp != NULL) {
    SET_P(PREC_P(succ_bp), NULL);
    lists[index] = succ_bp;
  } else if (prec_bp != NULL && succ_bp == NULL) {
    SET_P(SUCC_P(prec_bp), NULL);
  } else {

    lists[index] = NULL;
  }
  return;
}
