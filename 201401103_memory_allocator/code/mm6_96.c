/*
 * Name1: Rajdeep Pinge
 * Email1: 201401103@daiict.ac.in
 * Name2: Aditya Joglekar
 * Email1: 201401086@daiict.ac.in
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
	"Rajdeep-Aditya",
	/* First member's full name */
	"Rajdeep Santoshkumar Pinge",
	/* First member's email address */
	"201401103@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Aditya Vaibhav Joglekar",
	/* Second member's email address (leave blank if none) */
	"201401086@daiict.ac.in"
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
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

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
#define LISTS 10	//defines total number of lists we are making in the segregated free list implementation
#define MINSIZE 4*WSIZE		// minimum size of the free block 
/* header = WSIZE
*  previous free block pointer = WSIZE
*  next free block pointer = WSIZE
*  footer = WSIZE
*/

// set and get predecessor and successor pointers for doubly linked lists
#define PREV_FREE_BLK(bp)  (* ((unsigned int **) bp) )			//get previous free block in the linked list
#define NEXT_FREE_BLK(bp)  (* ((unsigned int **) bp + 1) )	//get next free block in the linked list

#define SET_PREV_FREE(bp, prev)  ( *((unsigned int **) bp) = (unsigned int *)prev)		//set previous free block in the linked list 
#define SET_NEXT_FREE(bp, next)  ( *((unsigned int **)bp + 1) = (unsigned int *)next)	//set next free block in the linked list



/* Global variables: */
static char *heap_listp; 	// Pointer to first block in the heap  
unsigned int **seg_free_list;	// pointer to (array of) pointers to all the linked lists
static char *epilogue_ptr;		// pointer to epilogue


/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static int checkblock(void *bp);
static int checkheap();
static void printblock(void *bp); 



/* Extra required functions to implement segregated free list*/
static void insert_seg_list(void *bp);
static void delete_seg_list(void *bp);
int find_list(size_t size);


/* Extra functions for optimization */
size_t extra_realloc_size(size_t size);
void explicit_print_list();
size_t round_size(size_t size);



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

	/* Create the initial empty heap. 
	* here we also allocate memory for pointers of segregated free list -> (LISTS * WSIZE)
	* this is because we are not allowed to use any memory outside the heap space
	*/
	if ((heap_listp = mem_sbrk(4 * WSIZE + LISTS * WSIZE)) == (void *)-1)	//in case mem_sbrk fails to allocate required memory for heap
		return (-1);	

	seg_free_list = (unsigned int **)(heap_listp);			//pointer at the start of the array of pointers to segregated free lists

	//initializing all the list pointers to null
	for(list = 0; list < LISTS; list++) {
		seg_free_list[list] = NULL;	
	}

	PUT(heap_listp + LISTS * WSIZE, 0);                            /* Alignment padding */
	PUT(heap_listp + ((LISTS + 1) * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + ((LISTS + 2) * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + ((LISTS + 3) * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += ((LISTS + 2) * WSIZE);
	epilogue_ptr = heap_listp + ((LISTS + 3) * WSIZE);

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

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/*to increase throughput we are rounding off the size to the nearest mutiple of WSIZE in the list class
	* Example: block of size >= .85 * 7 * WSIZE is rounded off to 8 * WSIZE
	*/	
	size = round_size(size); 

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

//* part which calls the heap checker function
/*	if ( checkheap() == 0) {
		printf("discrepency\n");
	}
*/
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
void *mm_realloc(void *ptr, size_t size)
{
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0){
        mm_free(ptr);
        return NULL;
    }

    //If the realloc'd block has previously been given more size than it needs
    // and now if it contains sufficient size, then
    // for this realloc request we need not find a new free block
    // we can directly use the current block 
    size_t currSize = GET_SIZE(HDRP(ptr));
    if (size < currSize-2*WSIZE) {		// currSize-2*WSIZE since the size of the block also contains size for header and footer
        return ptr;
    }
   
    // if the current size of the block is not sufficient,
    // check if the next block is free. If yes then check if the combined size of current and next block is sufficient or not
    // if yes then we need not search for a larger block and can simply address the realloc request by merging the current and next block
    void *next = NEXT_BLKP(ptr);
    int next_alloc = GET_ALLOC(HDRP(next));

    size_t coalesce_size = (GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr)));
    if (!next_alloc && size <= coalesce_size-2*WSIZE){		//if next block is free and size is sufficient
        delete_seg_list(next);				// if yes then remove the next block from the segregated free list
        PUT(HDRP(ptr), PACK(coalesce_size, 1));
        PUT(FTRP(ptr), PACK(coalesce_size, 1));
        return ptr;
    }

    //Assuming realloc will be called again in the future
    // try giving some extra size to the block so that some future realloc requests can be addressed in the same block
    size_t newSize = extra_realloc_size(size);
    
    /* If old ptr is NULL, then this is just malloc. */
    if (ptr == NULL)
        return (mm_malloc(newSize));

    void *oldptr = ptr;
    void *newptr;
    size_t oldSize;

    newptr = mm_malloc(newSize);
    if (newptr == NULL)
        return NULL;

    // Copy the old data.
    // decide the correct size
    oldSize = GET_SIZE(HDRP(oldptr));
    if (size < oldSize)
        oldSize = size;
    memcpy(newptr, oldptr, oldSize);
    
    // after copying the old data to the new block, free the old block
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
		// do nothing since we just want to insert this block in the free list which is done after the if-else-if ladder
	} 

	/* since next block is free, it must be in the segregated free list
	* remove that block from the list
	* coalesce with the current block and then put it back in the appropriate list class of the segregated free list
	*/
	else if (prev_alloc && !next_alloc) {         /* Case 2 */
		delete_seg_list(NEXT_BLKP(bp)); //delete the next block since it is being merged with the current block
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} 

	/* since previous block is free, it must be in the segregated free list
	* remove that block from the list
	* coalesce with the current block and then put it back in the appropriate list class of the segregated free list
	*/
	else if (!prev_alloc && next_alloc) {         /* Case 3 */
		delete_seg_list(PREV_BLKP(bp)); //delete the next block since it is being merged with the current block
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} 

	/* since both previous and next blocks are free, they must be in the segregated free list
	* remove those blocks from the list
	* coalesce with the current block and then put the merged block back in the appropriate list class of the segregated free list
	*/
	else {                                        /* Case 4 */
		delete_seg_list(NEXT_BLKP(bp)); //here both blocks will have to be removed.
		delete_seg_list(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	//put the merged block back in the segregated free list
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
	epilogue_ptr = HDRP(NEXT_BLKP(bp));

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}



/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */



//********************************************************************************************************************
/* 
*  finding appropriate list from which the block of desired size can be taken
*
*
*/
static void *
find_fit(size_t asize) {

/*	//first fit
	int list;
	void *bp = NULL;

	list = find_list(asize); //pointing to the list where search will start.

//we start from the list returned by the find list function. It is guarenteed that the searching in the lower lists will be futile. Then,
//we search a list. If not found, then we move onto the next until we find a free block.
	while(list < LISTS) {
		bp = (void *)seg_free_list[list];
		if(bp != NULL) {
			// Search for the first fit.
			for (; bp != NULL; bp = NEXT_FREE_BLK(bp)) {	
				if (asize <= GET_SIZE(HDRP(bp)) )
					return (bp);
			}
		}
		list++;
	}
	
	return NULL;
*/
//	"pseudo best-fit"
	int counter = 0; int threshold = 5; 
    //'threshold' is a small optimization that allows for a "pseudo best-fit" so that
    //LIFO lists can try doing better than always returning the first element.
    //This becomes important in larger-sized free lists where freeing and coalescing
    //patterns may create a very large initial block, requiring constant splicing and
    //re-insertions upon allocation.
    size_t lowest_diff = 9999999;
    void *bestSoFar = NULL;

    int index = find_list(asize);
    int i;
    for (i = index; i < LISTS; i++) { //start from index: if we don't find something in this 
        //size class, it can only be in a larger size class. Ideally could use size to just jump to the right
        //size class (TODO)
        void *bp = seg_free_list[i]; //start from the beginning
        while (bp) { //go through the linked list
            size_t curr_block_size = GET_SIZE(HDRP(bp));
            if (!GET_ALLOC(HDRP(bp)) && (asize <= curr_block_size)) {
                counter++; 
                size_t diff = curr_block_size - asize;
                if (diff < lowest_diff) { 
                    lowest_diff = diff;
                    bestSoFar = bp;
                }

                if (counter > threshold)
                    return bestSoFar; 

            }
            bp  = NEXT_FREE_BLK(bp);
        }
    }
    //Eventually if we don't find a fit, we will reach the end of the list, e.g. explicit list's next
    //will be NULL. Return NULL, find fit failed.
    return bestSoFar; 

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
	size_t currSize = GET_SIZE(HDRP(bp));	//current size of free block
	size_t sizeDiff = currSize - asize;	// size difference between required memory and available free memory block

	delete_seg_list(bp); // remove the block that allocated block from the correct list.   

     // Checks if the block can be split. If the size difference is greater than minimum size needed for the block,
     // we can split the block to get the block of precise size. 
     // If a new free block is made due to splitting, add it to the proper free list class
	if (sizeDiff >= MINSIZE) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(sizeDiff, 0));
		PUT(FTRP(bp), PACK(sizeDiff, 0));
		insert_seg_list(bp);
	} else {
	// if split is not possible allocate the whole free block
		PUT(HDRP(bp), PACK(currSize, 1));
		PUT(FTRP(bp), PACK(currSize, 1));
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
static int
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE) {
		printf("Error: %p is not doubleword aligned\n", bp);
		return 0;	
	}
	if (GET(HDRP(bp)) != GET(FTRP(bp))) {
		printf("Error: header does not match footer\n");
		return 0;
	}
	return 1;

}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
static int
checkheap(/*bool verbose*/) 
{
/*	void *bp;

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


	int list;

	for(list = 0; list<LISTS; list++) {
		
		for(bp = seg_free_list[list]; bp != NULL; bp = NEXT_FREE_BLK(bp)) {

			// to check if any free block has been wrongly marked as allocated
			if ( GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1 ) {
				printf("free block wrongly marked\n");
				return 0;
				//break;
			}

			// to check if there are adjacent free blocks which somehow missed coalescing
			if ( GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 || GET_ALLOC(FTRP(NEXT_BLKP(bp))) == 0 
				|| GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0 || GET_ALLOC(FTRP(PREV_BLKP(bp))) == 0 ) {
				printf("adjacent free blocks have not been coalesced\n");
				return 0;
				//break;
			}
		}
	}

	return 1;
	//printf("implementation of segregated free list is successful, there is no discrepency\n");
*/

    int i;

   epilogue_ptr=heap_listp;
 while(GET_SIZE(epilogue_ptr)!=0)
   	   epilogue_ptr=NEXT_BLKP(epilogue_ptr);

    for(i = 0; i < LISTS; i++) {
        void *bp = seg_free_list[i]; //start from the beginning

        while (bp) { //go through the linked list

            // CHECK 1 - check - is the block marked as free?
            if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1)
                return 0; //inconsistent, if in free list, should be marked free.

            //check - can we grab valid sizes from neighbouring contiguous blocks?
            int left_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
            int right_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
            if (left_size < 0 || right_size < 0)
                return 0; //invalid size somewhere in our list


	    // CHECK 2 is double word alignment satisfied? do the header and footer match?
	    if(checkblock(bp) == 0) 
		return 0;

	    //CHECK 3 have any blocks escaped coalescing?
	    if ( GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 || GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0 )
		return 0;

	    //CHECK 5 Assuming that only free blocks contain pointers in heap we only check whether they are pointing within heap or not
  
  // are all pointers valid?
/*if ( (NEXT_BLKP(bp) < (void *)seg_free_list) || (PREV_BLKP(bp) <(void *)seg_free_list)|| (NEXT_BLKP(bp) > epilogue_ptr) || (PREV_BLKP(bp)>(void *)epilogue_ptr)) 
		return 0;*/

            bp  = NEXT_FREE_BLK(bp);
        }
    }


    //CHECK 4 is every free block actually in the free list?
    void *curr = heap_listp, *bp;
    while(GET_SIZE(curr) != 0) {
	if(GET_ALLOC(curr) == 0) {	// that means if the block is free
		size_t size = GET_SIZE(curr);
		int list = find_list(size);

		bp = NULL;
		//search the block in the appropriate list class
	
        while (list<=LISTS)  	
          {
          for (bp = (void *)seg_free_list[list]; bp != NULL; bp = NEXT_FREE_BLK(bp)) {	
			if (bp == curr)
				break;
		}
         
                  list++;
          }
		if(bp == NULL && list>LISTS) {	//block is not in the list
			printf("free list discrepen\n");			
		return 0;
		}		
	}
	curr = NEXT_BLKP(curr);
    }	


//	explicit_print_list();
    return 1; //made it to the end, heap consistent.

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
/*	bool halloc, falloc;
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
*/

	printf("curr_block: %p @size: %lu <-->", bp, GET_SIZE(HDRP(bp)));
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

//the block can be inserted either at the beginning of the list, or by ordering it according to its size or by ordering it according to 
//its address.
static void insert_seg_list(void *bp) {
	size_t size = GET_SIZE(HDRP(bp));
	int list;
	
// LIFO or first-fit implemetation of insertion of free block into appropriate list class	
	unsigned int *reqdList = NULL;

	list = find_list(size);
	reqdList = seg_free_list[list];

	//reinserting at the start

	SET_NEXT_FREE(bp, reqdList);
	if(reqdList != NULL)
		SET_PREV_FREE(reqdList, bp);
	SET_PREV_FREE(bp, NULL);
	seg_free_list[list] = (unsigned int *) bp;


/*	
* byte size ascending order arrangement of the free blocks in the appropriate list class is enforced
*/
/*	void *curr, *insert_pos;

	list = find_list(size);
	curr = seg_free_list[list];

	if(curr == NULL) {	//means that particular list is empty
		SET_NEXT_FREE(bp, NULL);
		SET_PREV_FREE(bp, NULL);
		seg_free_list[list] = bp;
		return;
	}

	insert_pos = NULL;

	while(curr != NULL && (size > GET_SIZE(HDRP(curr))) ) {
		insert_pos = curr;	
		curr = NEXT_FREE_BLK(curr);
	}

	if(insert_pos != NULL && curr == NULL) {	//means it is the last block
		SET_NEXT_FREE(insert_pos, bp);
		SET_PREV_FREE(bp, insert_pos);
		SET_NEXT_FREE(bp, NULL);
	}
	else if(insert_pos != NULL && curr != NULL) {		//means it is somewhere in the middle
		SET_NEXT_FREE(bp, NEXT_FREE_BLK(insert_pos));
		SET_PREV_FREE(NEXT_FREE_BLK(insert_pos), bp);
		SET_NEXT_FREE(insert_pos, bp);
		SET_PREV_FREE(bp, insert_pos);
	}
	else if(insert_pos == NULL && curr != NULL) {	//means the block must be inserted first but the list is not empty
		SET_NEXT_FREE(bp, seg_free_list[list]);
		SET_PREV_FREE(seg_free_list[list], bp);
		SET_PREV_FREE(bp, NULL);
		seg_free_list[list] = bp;	
	}
*/
}

//routine to delete the block from the appropriate list. A block may have to be deleted if it has been allocated or has been coalesced
//into a larger block.
static void delete_seg_list(void *bp) {
	int list = 0;
	size_t size = GET_SIZE(HDRP(bp));

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

//function to choose the appropriate list. We pick a list to start the search based on its size. We can then ignore the lower lists
//as they will contain blocks which will be smaller than the current block.
int find_list(size_t size) {
/*	int list = 0;

	while(list < LISTS-1 && size >= 2*MINSIZE) {
		list++;
		size >>= 1;
	} 

	return list;
*/
/*	if (size > 2048*WSIZE) {
		return 19;
	}
	else if (size > 1024*WSIZE) {
		return 18;
	}
	else if (size > 512*WSIZE) {
		return 17;
	}
	else if (size > 256*WSIZE) {
		return 16;
	}
	else if (size > 128*WSIZE) {
		return 15;
	}
	else if (size > 64*WSIZE) {
		return 14;
	}
	else if (size > 32*WSIZE) {
		return 13;
	}
	else if (size > 28*WSIZE) {
		return 12;
	}
	else if (size > 24*WSIZE) {
		return 11;
	}
	else if (size > 20*WSIZE) {
		return 10;
	}
	else if (size > 16*WSIZE) {
		return 9;
	}
	else if (size > 13*WSIZE) {
		return 8;
	}
	else if (size > 10*WSIZE) {
		return 7;
	}
	else if (size > 9*WSIZE) {
		return 6;
	}
	else if (size > 8*WSIZE) {
		return 5;
	}
	else if (size > 7*WSIZE) {
		return 4;
	}
	else if (size > 6*WSIZE) {
		return 3;
	}
	else if (size > 5*WSIZE) {
		return 2;
	}
	else if (size > 4*WSIZE) {
		return 1;
	}
	else {
		return 0;
	}
*/

	if (size > 4096*WSIZE) {
		return 9;
	}
	else if (size > 2048*WSIZE) {
		return 8;
	}
	else if (size > 1024*WSIZE) {
		return 7;
	}
	else if (size > 512*WSIZE) {
		return 6;
	}
	else if (size > 256*WSIZE) {
		return 5;
	}
	else if (size > 128*WSIZE) {
		return 4;
	}
	else if (size > 64*WSIZE) {
		return 3;
	}
	else if (size > 32*WSIZE) {
		return 2;
	}
	else if (size > 16*WSIZE) {
		return 1;
	}
	else {
		return 0;
	}
}

//the basic logic is that if we allocate a little extra space during a call to reallocation, it may be possible to service the 
//future reallocation requests in the same block itself. This can significantly reduce the processing time and thus improve the through-put. When we implemented this scheme the overall score jumped from 36 to 92. 
size_t extra_realloc_size(size_t size) {

    size_t biggerBuffer = size * 16; //an arbitrary factor, we tried other factors, this seems to be the best one.
    //Assuming one would want to realloc into a size class somewhat more than twice the previous size.
    //This is in line with common use cases such as extending an array (e.g. C++ vectors)

    //But we will clamp that extra amount in multiples of page size
    if (biggerBuffer > size+24576) { //currently at 6 pages
        biggerBuffer = size+24576;
    }

    return biggerBuffer;

}

//if size is greater than 85% of the next class size, it means that the size is closer to the next size. So it is better placed in the next list. 
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

/**********************************************************
 * explicit_print_list
 * FOR DEBUG PURPOSES ONLY
 **********************************************************/
void explicit_print_list() {

    printf("====== FREE LIST: =========\n");
    int i;
    for(i = 0; i < LISTS; i++) {
        printf("\n---Free list #%d\n",i);
        void *bp = seg_free_list[i]; //start from the beginning
        while (bp) { //go through the linked list
//            printf("curr_block: %p @size: %lu <-->", bp, GET_SIZE(HDRP(bp)));
	    printblock(bp);
            bp  = NEXT_FREE_BLK(bp);
        }
    }
    printf("======== </FREE_LIST> =======\n");

}

