/*
 * Name: Rajdeep Pinge
 * Email: 201401103@daiict.ac.in
 *
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Shodh",
	/* First member's full name */
	"Rajdeep Santoshkumar Pinge",
	/* First member's email address */
	"201401103@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"",
	/* Second member's email address (leave blank if none) */
	""
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))		//changed from (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Some extra Macros */
#define LISTS 10	//defines number of lists we are making change from 16 to 10
#define MINSIZE 4*WSIZE

//#define PUT_PTR(p, val)  (*(unsigned int **)(p) = (val))	

// Predecessor and successor pointers for doubly linked lists

#define PREV_FREE_BLK(bp)  (* ((void **) bp) )
#define NEXT_FREE_BLK(bp)  (* ((void **) (bp + WSIZE)) )

#define SET_PREV_FREE(bp, prev)  ( *((void **) bp) = prev)
#define SET_NEXT_FREE(bp, next)  ( *((void **) (bp + WSIZE)) = next)


/* Global variables: */
static char *heap_listp; /* Pointer to first block */  

unsigned int **seg_free_list;	/* pointer to (array of) pointers to all the linked lists */

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
size_t extra_realloc_size(size_t size);
size_t round_size(size_t size);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* Extra required functions */
static void insert_seg_list(void *bp);
static void delete_seg_list(void *bp);
//long power(int a, int b);
int find_list(size_t size);

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{
	int list = 0;
/*	for(list = 0; list < LISTS; list++) {
		seg_free_list[list] = NULL;
	}
*/
	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE + LISTS * WSIZE)) == (void *)-1)
		return (-1);	

	seg_free_list = (unsigned int **)(heap_listp);			//pointing at the start
	for(list = 0; list < LISTS; list++) {
		seg_free_list[list] = NULL;
//		printf("%d\n", (*(int *)seg_free_list[list]) ); 	
	}

	PUT(heap_listp + list * WSIZE, 0);                            /* Alignment padding */
	PUT(heap_listp + ((list + 1) * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + ((list + 2) * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + ((list + 3) * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += ((list + 2) * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

size=round_size(size);

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);

//	insert_seg_list(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
 
/*void mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	// If size == 0 then this is just free, and we return NULL. 
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	// If oldptr is NULL, then this is just malloc. 
	if (ptr == NULL)
		return (mm_malloc(size));

	newptr = mm_malloc(size);

	// If realloc() fails the original block is left untouched  
	if (newptr == NULL)
		return (NULL);

	// Copy the old data. 
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	// Free the old block. 
	mm_free(ptr);

	return (newptr);
}*/

//new realloc
void *mm_realloc(void *ptr, size_t size)
{
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0){
        mm_free(ptr);
        return NULL;
    }

    //If the realloc'd block has previously been given more size than it needs, perhaps
    //this realloc request can be serviced within the same block:
    size_t curSize = GET_SIZE(HDRP(ptr));
    if (size < curSize-2*WSIZE) {
        return ptr;
    }
   
    void *next = NEXT_BLKP(ptr);
    int next_alloc = GET_ALLOC(HDRP(next));

    size_t coalesce_size = (GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr)));
    if (!next_alloc && size <= coalesce_size-2*WSIZE){
        delete_seg_list(next);
        PUT(HDRP(ptr), PACK(coalesce_size, 1));
        PUT(FTRP(ptr), PACK(coalesce_size, 1));
        return ptr;
    }

    //Assuming realloc will be called again in the future, try giving a bigger block to use:
    size_t newSize = extra_realloc_size(size);
    
    /* If old ptr is NULL, then this is just malloc. */
    if (ptr == NULL)
        return (mm_malloc(newSize));

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(newSize);
    if (newptr == NULL)
        return NULL;

    /* Copy the old data. */
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}




/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		insert_seg_list(bp);
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		delete_seg_list(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		delete_seg_list(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		delete_seg_list(NEXT_BLKP(bp));
		delete_seg_list(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
/*
	if( last_listp < NEXT_BLKP(bp) && last_listp > (char*)(bp) ) {
		last_listp = bp;
	}
*/
	insert_seg_list(bp);
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

size_t round_size(size_t size) {

    if (size > 435 && size < 512)
        return 512;

    if (size > 870 && size < 1024)
        return 1024;

    if (size > 1741 && size < 2048)
        return 2048;

    if (size > 3482 && size < 4096)
        return 4096;

    if (size > 6963 && size < 8192)
        return 8192;

    return size;
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
/*static void *
find_fit(size_t asize)
{
	void *bp;

	***** Search for the first fit. */
/*	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
			return (bp);
	}
	****** No fit was found. */
/*	return (NULL);
}
*/





/*
 * This follows best fit allocation
 *
 *
 *
 */
/*static void * find_best_fit(size_t asize) {
	void *bp;
	size_t minSize = 100000000;
	void *min_bp = NULL;

	** search for the best fit */
/*	for ( bp = heap_listp; GET_SIZE(HDRP(bp)) ; bp = NEXT_BLKP(bp) ) {		//limiting condition is size > 0 since end block of heap has size 0
		if ( !GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
			if (GET_SIZE(HDRP(bp)) < minSize) {
				minSize = GET_SIZE(HDRP(bp));
				min_bp = bp;
			}
		}
	}

	if(min_bp == NULL) {
		return NULL;
	}

	else {
		return min_bp;
	}
}
*/





/*
 * next fit algorithm
 *
 *
 *
 *
 */
/*static void *find_fit(size_t asize) {
	void *bp;  

*/	/* Search for the first fit. */
/*	for (bp = last_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	       	if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
			last_listp = NEXT_BLKP(bp);
                	return (bp);
		}
        }
*/
	//restart from beginning of the list

        /* Search for the next fit. */
/*	for (bp = heap_listp; bp != last_listp; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
         		last_listp = NEXT_BLKP(bp); 
			return (bp);
		}
	}   

*/	/* No fit was found. */
/*	return (NULL);
}
*/





/* 
*  finding appropriate list from which the block of desired size can be taken
*
*
*/
static void *
find_fit(size_t asize) {
	int list;
	unsigned int *reqdList = NULL;
	void *bp = NULL;

	list = find_list(asize);
//	reqdList = seg_free_list[list];

	while(list < LISTS) {
		reqdList = seg_free_list[list];
		if(reqdList != NULL) {
			/* Search for the first fit. */
			for (bp = (void *)reqdList; bp != NULL; bp = NEXT_FREE_BLK(bp)) {	//check corner case of last block
				if (asize <= GET_SIZE(HDRP(bp)) )
					return (bp);
			}
			/* No fit was found. */
/*			if(bp == NULL) {
				list++;
				continue;
			}
*/		}
		list++;

	}
/*
	for(list = 0; list < LISTS-1; list++) {
		if((long)asize < power(2, list+3) ) {
			reqdList = seg_free_list[list];
			
			if(reqdList != NULL) {
				// Search for the first fit.
				for (bp = reqdList; bp != NULL; bp = NEXT_FREE_BLK(bp)) {	//check corner case of last block
					if (asize <= GET_SIZE(HDRP(bp)) )
						return (bp);
				}
				// No fit was found.
				if(bp == NULL) {
					continue;
				}
			}
		}
	}

	if(list == LISTS-1) {
		reqdList = seg_free_list[LISTS-1];
			
		if(reqdList != NULL) {
			// Search for the first fit.
			for (bp = reqdList; bp != NULL; bp = NEXT_FREE_BLK(bp)) {	//check corner case of last block
				if (asize <= GET_SIZE(HDRP(bp)) )
					return (bp);
			}
		}
	}
*/	
	return NULL;
}


/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
	size_t sizeDiff = csize - asize;

	delete_seg_list(bp);   

	if (sizeDiff >= MINSIZE) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(sizeDiff, 0));
		PUT(FTRP(bp), PACK(sizeDiff, 0));
		insert_seg_list(bp);
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */


/* Extra required functions */
static void insert_seg_list(void *bp) {
	size_t size = GET_SIZE(HDRP(bp));
	int list;
	unsigned int *reqdList = NULL;

/*	for(list = 0; list < LISTS-1; list++) {
		if((long)size >= power(2,list+2) && (long)size < power(2, list+3) ) {
			break;
		}
	}
*/
	list = find_list(size);
	reqdList = seg_free_list[list];

	//reinserting at the start

	SET_NEXT_FREE(bp, reqdList);
	if(reqdList != NULL)
		SET_PREV_FREE(reqdList, bp);
	SET_PREV_FREE(bp, NULL);
	seg_free_list[list] = (unsigned int *) bp;

}

static void delete_seg_list(void *bp) {
	int list = 0;
	size_t size = GET_SIZE(HDRP(bp));

/*	for(list = 0; list < LISTS-1; list++) {
		if((long)size >= power(2,list+2) && (long)size < power(2, list+3) ) {
			break;
		}
	}
*/

	list = find_list(size);

	if(PREV_FREE_BLK(bp) != NULL) {
		if(NEXT_FREE_BLK(bp) != NULL) {
			SET_PREV_FREE(NEXT_FREE_BLK(bp), PREV_FREE_BLK(bp));
			SET_NEXT_FREE(PREV_FREE_BLK(bp), NEXT_FREE_BLK(bp));
		}
		else {
			SET_NEXT_FREE(PREV_FREE_BLK(bp), NULL);
		}
	}
	else {
		if(NEXT_FREE_BLK(bp) != NULL) {
			SET_PREV_FREE(NEXT_FREE_BLK(bp), NULL);
			seg_free_list[list] = (unsigned int *)NEXT_FREE_BLK(bp);
		}
		else {
			seg_free_list[list] = NULL;
		}
	}
}


/*int find_list(size_t size) {
	int list = 0;

	while(list < LISTS-1 && size >= 2*MINSIZE) {
		list++;
		size >>= 1;
	} 

	return list;
}*/

int find_list(size_t size) {
	 if (size > 16384)
        return 9;
    else if (size > 8192)
        return 8;
    else if (size > 4096)
        return 7;
    else if (size > 2048)
        return 6;
    else if (size > 1024)
        return 5;
    else if (size > 512)
        return 4;
    else if (size > 256)
        return 3;
    else if (size > 128)
        return 2;
    else if (size > 64)
        return 1;
    else
        return 0;
}


size_t extra_realloc_size(size_t size) {

    size_t biggerBuffer = size * 4; 
    //Assuming one would want to realloc into a size class somewhat more than twice the previous size.
    //This is in line with common use cases such as extending an array (e.g. C++ vectors)

    //But we will clamp that extra amount in multiples of page size
    if (biggerBuffer > size+24576) { //currently at 6 pages
        biggerBuffer = size+24576;
    }

    return biggerBuffer;

}

/*
long power(int a, int b) {
	long power = 1;
	while(b > 0) {
		power *= a;
		b--;
	}
	return power;
}*/
