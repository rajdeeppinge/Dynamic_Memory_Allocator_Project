/*ive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this approach, the outline of the block is such that, payload 
 * is used to store prev and next pointers of the prev and next free block,
 * if the block is free. There are macros defined which compute the address
 * of previous and next free block, only if the blocks are free.
 * Then, a explicit free list is maintained in which the block pointer is added  if the block is free and is removed if it gets allocated. 
 *Two functions, insert_free_list and delete_free_list are defined to maintain the explicit free list
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"


team_t team = {
    /* Team name */
    "Tarang Patel",
    /* First member's full name */
    "Tarang Patel",
    /* First member's email address */
    "201101110@daiict.ac.in",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};



/* size of word */
#define WSIZE sizeof(void*)

/* size of double word */
#define DSIZE 2*WSIZE


/* rounds up to the nearest multiple of DSIZE */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~(DSIZE-1))
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Initial size of heap (for expanding) */
#define CHUNKSIZE (1 << 12) 
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Extra bytes used by header and footer */
#define OVERHEAD DSIZE

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (* ((unsigned int *) (p)))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) ((unsigned int)GET(p) & ~(DSIZE-1))
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block pointer bp, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - 2*WSIZE)

/* Given block pointer bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void*)(bp) + GET_SIZE(((void *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((void*)(bp) - GET_SIZE(((void *)(bp) - 2*WSIZE)))

/* Given a header pointer ptr, compute address of NEXT and PREV blocks.*/

#define PREV_FREE_BLKP(ptr) (*(void **) (ptr))
#define NEXT_FREE_BLKP(ptr) (*(void **) (ptr + WSIZE))

/* Given a header pointer ptr, set the NEXT and PREV pointers to their new addresses.*/

#define SET_PREV_FREE(bp, prev) (*((void **)(bp)) = prev) 
#define SET_NEXT_FREE(bp, next) (*((void **)(bp + WSIZE)) = next) 

static void *free_list_head; /* Points to the first block in the free list.*/
static void *heap_listp; /* Points to the prologue block.*/

/* function declarations */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);

static void delete_list(void *bp);
static void insert_list(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {

       
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL) {
        return -1;
    }
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(OVERHEAD, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(OVERHEAD, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    
    heap_listp += DSIZE;
    
    free_list_head = NULL;
    if ((extend_heap(CHUNKSIZE/WSIZE)) == NULL) {
        return -1;
    }
    
    return 0;
}

/*
 Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    
    size_t asize; 
    size_t extendsize; 
    void *bp;
    
    if (size <= 0) {
        return NULL;
    }
    
    /* Adjust block size to include overhead, alignment requirements*/
    if (size <= DSIZE) {
        asize = 2 * DSIZE; 
    } else {
        asize = ALIGN(size + (2 * WSIZE)); /* Add in overhead bytes and round up to nearest multiple of DSIZE */
    }
    
    /* Search free list for a fit*/
    if ((bp = find_fit(asize)) != NULL) {
        bp = place(bp, asize);
        return bp;
    }
    
    /* No fit found. Get more meomory and place the block. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL; /* No more heap space */
    }
    bp = place(bp, asize);
    
    return bp;
}

/* frees a block of memory */
void mm_free(void *ptr) {
	size_t size = GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);
}



/* Extends the heap with a new free block */
static void *extend_heap(size_t words) {
    
    void *bp;
    size_t size;
    
    size = ALIGN(words * WSIZE);
    if ((long)(bp =  mem_sbrk(size)) == -1) { 
        return NULL;
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    
    /* Coalesce if previous block was free */
    return coalesce(bp);
}

/* Merges adjacent free block maintains explicit free list */
  
static void *coalesce(void *bp) {
    
    size_t next_alloc = GET_ALLOC((void *)(FTRP(bp)) + WSIZE);
    size_t prev_alloc = GET_ALLOC((void *)(bp) - 2*WSIZE);
    size_t size = GET_SIZE(HDRP(bp));
      
       if (prev_alloc && next_alloc) { /* Case 1: If both previous and next blocks allocated  */
          insert_list(bp); /* Insert bp at starting of the list.*/
      } else if (prev_alloc && !next_alloc) { /* Case 2: If next block is free, coalesce with the next. */
          delete_list(NEXT_BLKP(bp));
          size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
          PUT(HDRP(bp), PACK(size, 0)); 
          PUT(FTRP(bp), PACK(size, 0)); 
          
          insert_list(bp); /* Insert bp at the starting of list.*/
      
      } else if (!prev_alloc && next_alloc) { /* Case 3: If previous block free, coalesce with previous */
          size += GET_SIZE(HDRP(PREV_BLKP(bp)));
          PUT(FTRP(bp), PACK(size, 0)); 
          PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
          bp = PREV_BLKP(bp);
      } else { /* Case 4: If both previous and next blocks free */
          
          delete_list(NEXT_BLKP(bp)); 
          size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
          PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
          PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); 
          bp = PREV_BLKP(bp);
      }
  
      return bp;

}

/* Remove a block pointer bp from the free list */
 
static void delete_list(void *bp) {
    
    void *next = (void *) NEXT_FREE_BLKP(bp);
    void *prev = (void *) PREV_FREE_BLKP(bp);
    if (prev == NULL) { 
        free_list_head = next;
    } else {
        SET_NEXT_FREE(prev, next);
    }
    
    if (next != NULL) { 
        SET_PREV_FREE(next, prev);
    }
}

/* Add the block pointer bp to the free list */
static void insert_list(void *bp) {
    void *current = free_list_head;
    void *temp = current;
    void *prev = NULL;
    while (current != NULL && bp < current) {
        prev = PREV_FREE_BLKP(current);
        temp = current;
        current = NEXT_FREE_BLKP(current);
    }
    
    SET_PREV_FREE(bp, prev);
    SET_NEXT_FREE(bp, temp);
    if (prev != NULL) {
        SET_NEXT_FREE(prev, bp);
    } else { 
        /* Insert bp before current free list head*/
        free_list_head = bp;
    }
    if (temp != NULL) {
        SET_PREV_FREE(temp, bp);
    }
}


/* Search the free list for a free block big enough to fit asize. It returns a pointer to the block if
*/
static void *find_fit(size_t asize) {
	void *bp;
	for(bp = free_list_head; bp != NULL; bp = NEXT_FREE_BLKP(bp)) {
		if(asize <= GET_SIZE(HDRP(bp))) {
			return bp;
		}
	}
	return NULL; 
}


static void *place(void *bp, size_t asize) {

	size_t csize = GET_SIZE(HDRP(bp));
	if (csize - asize >= (DSIZE + OVERHEAD)) { 
		delete_list(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		void *original_bp = bp;
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		insert_list(bp);
		bp = original_bp;
	} else { 
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		delete_list(bp);
	} 
	return bp;
}


/*  reallocates a memory block to update it with the given size */
void *mm_realloc(void *ptr, size_t size) {

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
     
    if(size <= 0 ){
    mm_free(ptr);
    return NULL;
     }
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
 	}
