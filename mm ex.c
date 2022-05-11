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
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


/* single word (4) or double word (8) alignment */
#define WSIZE sizeof(void *)
#define DSIZE (2*WSIZE)
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

// read and write a word at address p
#define GET(p) (*(uintptr_t *)(p))
#define PUT(p, val) (*(uintptr_t *)(p) = (val))

// read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p) (GET(p) & 0x1)

// given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

// given free block ptr bp, get next, prev free block pointer
#define NEXT_FREE_BLKP(bp) (*(char **)(bp + WSIZE))
#define PREV_FREE_BLKP(bp) (*(char **)(bp))

// set pointers in the next and previous elements of free list
#define SET_NEXT_FREE_BLKP(p, q) (NEXT_FREE_BLKP(p) = q)
#define SET_PREV_FREE_BLKP(p, q) (PREV_FREE_BLKP(p) = q)

static char *heap_listp = 0;
static char *ROOT = 0;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void insert_block(void *bp);
static void remove_block(void *bp);


static bool debugging = false;

void mm_checkheap(int lineno)
{
    printf("checkheap from %d\n", lineno);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
        return -1;


    if (debugging)
        printf("mm_init call\n");


    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));     
    PUT(heap_listp + 2*WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 3*WSIZE, PACK(0, 1));
    
    ROOT = heap_listp + 2*WSIZE;

    if (extend_heap(4) == NULL) {
        return -1;
    }

    if (debugging) {
        printf("ROOT %p\n", ROOT);
        printf("next_ROOT %p\n", NEXT_FREE_BLKP(ROOT));
        printf("prev_next_ROOT %p\n", PREV_FREE_BLKP(NEXT_FREE_BLKP(ROOT)));
    }
    return 0;
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if (debugging)
        printf("mm_malloc\n");

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        asize = 2*DSIZE;
    }
    else {
        asize = ((size + (DSIZE) + (DSIZE-1)) / DSIZE) * DSIZE;
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    // mm_checkheap(__LINE__);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (bp == NULL)
        return;
    size_t size = GET_SIZE(HDRP(bp));
    // printf("mm_free call\n");
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
    // mm_checkheap(__LINE__);
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) {
    if ((int)size < 0)
        return NULL;
    
    else if ((int)size == 0) {
        mm_free(bp);
        return NULL;
    }

    else if (size > 0) {
        size_t oldsize = GET_SIZE(HDRP(bp));
        size_t newsize = size + 2*WSIZE;

        if (newsize <= oldsize)
            return bp;

        else {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
            size_t csize;
            csize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(bp)));
            if (!next_alloc && (csize >= newsize)) {
                remove_block(NEXT_BLKP(bp));
                PUT(HDRP(bp), PACK(csize, 1));
                PUT(FTRP(bp), PACK(csize, 1));
                return bp;
            }
            else {
                void *newptr = mm_malloc(newsize);
                place(newptr, newsize);
                memcpy(newptr, bp, newsize);
                mm_free(bp);
                return newptr;
            }
        }
    }
    else
        return NULL;

}

static void *coalesce(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if (debugging) {
        printf("coalesce call\n");
    }

    if (prev_alloc && next_alloc) {
        // printf("coalesce case 1\n");
        insert_block(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        // printf("coalesce case 2\n");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_block(NEXT_BLKP(bp));
    }
    else if (!prev_alloc && next_alloc) {
        // printf("coalesce case 3\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_block(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc) {
        // printf("coalesce case 4\n");
        // printf("%p %p\n", bp, next_free_bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_block(bp);
    return bp;
}


static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    if (debugging)
        printf("extend heap call\n");

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (size < 16)
        size = 16;
    
    if ((bp = mem_sbrk(size)) == (void *)-1) 
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}


static void *find_fit(size_t asize)
{
    void *bp;

    if (debugging)
        printf("find fit call\n");

    for (bp=ROOT; GET_ALLOC(HDRP(bp)) == 0; bp=NEXT_FREE_BLKP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if (debugging)
        printf("place call\n");
    
    if ((csize - asize) >= (4*WSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_block(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_block(bp);
    }
}


static void insert_block(void *bp)
{
    if (debugging) {
        printf("insert call\n");
        printf("%p\n", NEXT_FREE_BLKP(bp));
        printf("%p\n", PREV_FREE_BLKP(NEXT_FREE_BLKP(bp)));
        printf("%p %p\n", ROOT, bp);
    }

    SET_NEXT_FREE_BLKP(bp, ROOT);
    SET_PREV_FREE_BLKP(ROOT, bp);
    SET_PREV_FREE_BLKP(bp, NULL);
    ROOT = bp;

    if (debugging) {
        printf("%p %p\n", ROOT, NEXT_FREE_BLKP(bp));
    }
}


static void remove_block(void *bp)
{
    if (debugging) {
        printf("remove call\n");
        printf("%p %p %p %p\n", bp, NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(bp), ROOT);
    }

    if (PREV_FREE_BLKP(bp))
        SET_NEXT_FREE_BLKP(PREV_FREE_BLKP(bp), NEXT_FREE_BLKP(bp));
    else
        ROOT = NEXT_FREE_BLKP(bp);
    PREV_FREE_BLKP(NEXT_FREE_BLKP(bp)) = PREV_FREE_BLKP(bp);
}
