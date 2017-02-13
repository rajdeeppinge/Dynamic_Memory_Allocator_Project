/*
 * Name1: Rajdeep Pinge
 * ID1: 201401103
 * Email1: 201401103@daiict.ac.in
 * Name2: Aditya Joglekar
 * ID2: 201401086
 * Email2: 201401086@daiict.ac.in
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
#define NUM_LISTS 12	//defines total number of lists we are making in the segregated free list implementation
			// 10-20 list-classes give the optimum experimental result. We even tried with 10, 11, 14, 15, 16 and 20 lists.

/* Minimum size of the free block
*  header = WSIZE
*  previous free block pointer = WSIZE
*  next free block pointer = WSIZE
*  footer = WSIZE
*/
#define MINSIZE 4*WSIZE	 


// set and get predecessor and successor pointers for doubly linked lists
#define GET_PREV_FREE_BLK(bp)  (* ((unsigned int **) bp) )	//get previous free block in the linked list
#define GET_NEXT_FREE_BLK(bp)  (* ((unsigned int **) bp + 1) )	//get next free block in the linked list

#define SET_PREV_FREE_BLK(bp, prev)  ( *((unsigned int **) bp) = (unsigned int *)prev)	//set previous free block in the linked list 
#define SET_NEXT_FREE_BLK(bp, next)  ( *((unsigned int **)bp + 1) = (unsigned int *)next)	//set next free block in the linked list



/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
unsigned int **seg_free_list;	/* pointer to (array of) pointers to all the linked lists */



/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_free_block(size_t asize);
static void place_allocated_block(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
/*****************************************************************************************************************
* NOTE: Here we have commented out all the heap checker function calls.
* This is because, as suggested in the project manual, we removed all the calls to these functions 
* but this gives a warning which is conveted to an ERROR due to the -Werror tag in the compilation code declared in the Makefile.txt
*******************************************************************************************************************/
//static int checkblock(void *bp);
//static int checkheap();
//static void printblock(void *bp); 
//static int check_seg_list_ptrs();
//static int check_size();
//static int check_free_block_in_heap();
//static int check_pointer_validity();

/* Extra required functions to implement segregated free list*/
static void insert_block_in_seg_list(void *bp);
static void delete_block_from_seg_list(void *bp);
int find_list_class(size_t size);




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
	* here we also allocate memory for pointers of segregated free list -> (NUM_LISTS * WSIZE)
	* this is because we are not allowed to use any memory outside the heap space
	*/
	if ((heap_listp = mem_sbrk(4 * WSIZE + NUM_LISTS * WSIZE)) == (void *)-1)	//in case mem_sbrk fails to allocate required memory for heap
		return (-1);	

	seg_free_list = (unsigned int **)(heap_listp);	//pointer at the start of the array of pointers to segregated free lists

	//initializing all the list pointers to null
	for(list = 0; list < NUM_LISTS; list++) {
		seg_free_list[list] = NULL;	
	}

	// now the actual heap implementation starts
	PUT(heap_listp + NUM_LISTS * WSIZE, 0);                      /* Alignment padding */
	PUT(heap_listp + ((NUM_LISTS + 1) * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + ((NUM_LISTS + 2) * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + ((NUM_LISTS + 3) * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += ((NUM_LISTS + 2) * WSIZE);

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
	

	/* Search the free list for a fit. */
	if ((bp = find_free_block(asize)) != NULL) {
		place_allocated_block(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place_allocated_block(bp, asize);
	
	//check_seg_list_ptrs();	//checker function to verify the validity of segregated free list pointers
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

// part which calls the heap checker function
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

	//If the previous block somehow already has more size than it needs without the knowledge of user, then
	// for this realloc request we need not find a new free block
	// we can directly use the current block 
	size_t currSize = GET_SIZE(HDRP(ptr));
	if (size < currSize-2*WSIZE) {		// currSize-2*WSIZE since the size of the block also contains size for header and footer
		return ptr;
	}

	// if the current size of the block is not sufficient,
	// check if the next block is free. If yes then check if the combined size of current and next block is sufficient or not
	// if yes then we need not search for a larger block and can simply address the realloc request by merging the current and next block
	// this saves us the time of recopying the whole block to some other place hence incresing the throughput
	void *next = NEXT_BLKP(ptr);

	size_t totalSize = (GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr)));
	if (!GET_ALLOC(HDRP(next)) && size <= totalSize-2*WSIZE){	//if next block is free and size is sufficient
		delete_block_from_seg_list(next);		// if yes then remove the next block from the segregated free list
		PUT(HDRP(ptr), PACK(totalSize, 1));
		PUT(FTRP(ptr), PACK(totalSize, 1));
		return ptr;
	}

	/* If old ptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	size_t oldSize;
	void *newptr;  

	newptr = mm_malloc(size);
	if (newptr == NULL)
		return NULL;

	// Copy the old data.
	// decide the correct size
	oldSize = GET_SIZE(HDRP(ptr));
	if (size < oldSize)
		oldSize = size;
	memcpy(newptr, ptr, oldSize);

	// after copying the old data to the new block, free the old block
	mm_free(ptr);
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

	/* Case 1 */
	if (prev_alloc && next_alloc) {                 
		// do nothing since we just want to insert this block in the free list which is done after the if-else-if ladder
	} 

	/* Case 2 - since next block is free, it must be in the segregated free list
	* remove that block from the list
	* coalesce with the current block and then put it back in the appropriate list class of the segregated free list
	*/
	else if (prev_alloc && !next_alloc) { 
		delete_block_from_seg_list(NEXT_BLKP(bp)); //delete the next block since it is being merged with the current block
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} 

	/* Case 3 - since previous block is free, it must be in the segregated free list
	* remove that block from the list
	* coalesce with the current block and then put it back in the appropriate list class of the segregated free list
	*/
	else if (!prev_alloc && next_alloc) { 
		delete_block_from_seg_list(PREV_BLKP(bp)); //delete the next block since it is being merged with the current block
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} 

	/* Case 4 - since both previous and next blocks are free, they must be in the segregated free list
	* remove those blocks from the list
	* coalesce with the current block and then put the merged block back in the appropriate list class of the segregated free list
	*/
	else {  
		delete_block_from_seg_list(NEXT_BLKP(bp)); //here both blocks will have to be removed.
		delete_block_from_seg_list(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	//put the merged block back in the segregated free list
	insert_block_in_seg_list(bp);
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



/*
 * Effects:
 *   As the name suggests, this function finds appropriate free block.  
 *   We have used first fit approach to find free block.
 *   We start our search ignoring the lists where we know that a large enough will not be found and run through the subsequent lists.
 *   Care has to be taken that the allocated block is removed from the appropriate list.
 */
static void *
find_free_block(size_t asize) {
	int list;
	void *bp = NULL;

	list = find_list_class(asize); //pointing to the list where search will start.

	//we start from the list returned by the find list-class function. 
	//It is guarenteed that the searching in the lower lists will be futile. Then,
	//we search a list. If not found, then we move onto the next until we find a free block.
	while(list < NUM_LISTS) {
		bp = (void *)seg_free_list[list];
		if(bp != NULL) {
			// Search for the first fit.
			for (; bp != NULL; bp = GET_NEXT_FREE_BLK(bp)) {	
				if (asize <= GET_SIZE(HDRP(bp)) )
					return (bp);
			}
		}
		list++;
	}
	
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
place_allocated_block(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));	//current size of free block

	delete_block_from_seg_list(bp); // remove the allocated block from the correct list.   

	// Checks if the block can be split. If the size difference is greater than minimum size needed for the block,
	// we can split the block to get the block of precise size. 
	// If a new free block is made due to splitting, add it to the proper free list class
	if ((csize - asize) >= MINSIZE) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		insert_block_in_seg_list(bp);	//insert the free block formed after splitting back into the appropriate segregated list
	} else {
		// if split is not possible allocate the whole free block
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}



/* Extra required functions */

//The block can be inserted either at the beginning of the list (LIFO implementation), 
//or by ordering it according to its address(address ordered implementation).
static void insert_block_in_seg_list(void *bp) {
	size_t size = GET_SIZE(HDRP(bp));
	int list_class;
	
	// LIFO or first-fit implemetation of insertion of free block into appropriate list class	
	unsigned int *reqdList = NULL;

	list_class = find_list_class(size);
	reqdList = seg_free_list[list_class];

	//inserting free block at the start of doubly linked list
	SET_NEXT_FREE_BLK(bp, reqdList);
	if(reqdList != NULL)
		SET_PREV_FREE_BLK(reqdList, bp);
	SET_PREV_FREE_BLK(bp, NULL);
	seg_free_list[list_class] = (unsigned int *) bp;

	// if we run the programme with the below mentined address ordered implementation, the utilisation actually reduces by 2 (changes from 31 to 29)
	//hence we haven't used this implementation
/*
	// address ordered implementation to insert free block
	list_class = find_list_class(size);

	unsigned int *curr = seg_free_list[list_class];
	unsigned int *prev = NULL;

	while(curr != NULL) {
		prev = GET_PREV_FREE_BLK(curr);
		if(bp < (void *)curr) {
			break;
		}
		curr = GET_NEXT_FREE_BLK(curr);
	}

	//so the block is to be inserted in between prev and curr pointers
	SET_NEXT_FREE_BLK(bp, curr);
	SET_PREV_FREE_BLK(bp, prev);

	if(prev == NULL) {		//that means we have to inset it at the start
		seg_free_list[list_class] = (unsigned int *)bp;		
	}
	else {
		SET_NEXT_FREE_BLK(prev, bp);
	}

	if(curr != NULL) {
		SET_PREV_FREE_BLK(curr, bp);
	}
*/	
}


//routine to delete the block from the appropriate list. 
// A block may have to be deleted if it has been allocated or has been coalesced into a larger block.
static void delete_block_from_seg_list(void *bp) {
	int list_class = 0;
	size_t size = GET_SIZE(HDRP(bp));

	list_class = find_list_class(size);

	// standard procedure to delete a block from a doubly linked list
	// there are four cases to be handled
	if(GET_PREV_FREE_BLK(bp) != NULL) {
		if(GET_NEXT_FREE_BLK(bp) != NULL) {
			SET_PREV_FREE_BLK(GET_NEXT_FREE_BLK(bp), GET_PREV_FREE_BLK(bp));
			SET_NEXT_FREE_BLK(GET_PREV_FREE_BLK(bp), GET_NEXT_FREE_BLK(bp));
		}
		else {
			SET_NEXT_FREE_BLK(GET_PREV_FREE_BLK(bp), NULL);
		}
	}
	else {
		if(GET_NEXT_FREE_BLK(bp) != NULL) {
			SET_PREV_FREE_BLK(GET_NEXT_FREE_BLK(bp), NULL);
			seg_free_list[list_class] = (unsigned int *)GET_NEXT_FREE_BLK(bp);
		}
		else {
			seg_free_list[list_class] = NULL;
		}
	}
}


/*
* we tried with different number of list-classes and classes with different length classes but
* the implemetation with 10-20 list classes gives optimum utilization result. Here we have used 12 list-classes.
*/
int find_list_class(size_t size) {
	if (size > 4096*WSIZE) {
		return 11;
	}
	else if (size > 2048*WSIZE) {
		return 10;
	}
	else if (size > 1024*WSIZE) {
		return 9;
	}
	else if (size > 512*WSIZE) {
		return 8;
	}
	else if (size > 256*WSIZE) {
		return 7;
	}
	else if (size > 128*WSIZE) {
		return 6;
	}
	else if (size > 64*WSIZE) {
		return 5;
	}
	else if (size > 32*WSIZE) {
		return 4;
	}
	else if (size > 16*WSIZE) {
		return 3;
	}
	else if (size > 8*WSIZE) {
		return 2;
	}
	else if (size > 6*WSIZE) {
		return 1;
	}
	else {
		return 0;
	}
}



/*****************************************************************************************************************
* NOTE: Here we have commented out all the heap checker functions.
* This is because, as suggested in the project manual, we removed all the calls to these functions 
* but this gives a warning which is conveted to an ERROR due to the -Werror tag in the compilation code declared in the Makefile.txt
* Hence to avoid this error it was necessary to perform this
*******************************************************************************************************************/

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
/*static int
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

}*/


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
/*static int
checkheap() 
{
	//traverse through all the segregated free list-classes 
	int list_class;

	for(list_class = 0; list_class < NUM_LISTS; list_class++) {
		void *bp = seg_free_list[list_class];

		while (bp != NULL) {

			// CHECK 1 - check - is the block marked as free?
			if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1)
				return 0; //inconsistent, if in free list, should be marked free.

			// CHECK 2 is double word alignment satisfied? do the header and footer match?
			if(checkblock(bp) == 0) 	//uses given checkblock function
				return 0;

			//CHECK 3 have any blocks escaped coalescing?
			if ( GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 || GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0 )
				return 0;

			bp  = GET_NEXT_FREE_BLK(bp);
		}
	}

	return 1; //made it to the end, heap consistent.
}*/


/*
*    for every free block in the heap, we check if the pointers used by the block are valid or not 
*/
/*static int check_pointer_validity()
{
			
	void * bp=heap_listp; 
	while (bp!=NULL) {
		void *next = (void *)NEXT_BLKP(bp);
		void *prev = (void *)PREV_BLKP(bp);

		if (next!=NULL && prev!=NULL) {
			if ( (next < mem_heap_lo()) || (prev < mem_heap_lo())|| (next > mem_heap_hi()) || (prev > mem_heap_hi()))
			printf("invalid pointers\n"); 
		}
		bp=GET_NEXT_BLK_PTR(bp);
	}
}*/

/*
* This function checks if all the block in the heap have valid sizes
*/
/*
static int check_size() {

	//traverse through the whole heap 
	void *curr = heap_listp;
	while( curr < mem_heap_hi() ) {
		if( (long)GET_SIZE(curr) < 0) {
			printf("Invalid size\n");
			return 0;
		}
		curr = NEXT_BLKP(curr);
	}

	return 1;	// all block have valid sizes
}
*/

/*
* To check if all the free blocks present in heap are actually in the free list
*/
/*
static int check_free_block_in_heap() {

	//traverse through the whole heap
	void *curr = heap_listp, *bp;
	
	while( curr < mem_heap_hi() ) {
		if(!GET_ALLOC(curr)) {	// that means if the block is free
			size_t size = GET_SIZE(curr);		//get the size of block
			int list = find_list_class(size);	//find its associated list class in which block must be present

			bp = NULL;

			//search the block in the appropriate list-class
			for (bp = (void *)seg_free_list[list]; bp != NULL; bp = GET_NEXT_FREE_BLK(bp)) {	
				if (bp == curr)
					break;
			}

			if(bp == NULL) {	//block is not in the list
				printf("free list discrepeny\n");			
				return 0;
			}		
		}
		curr = NEXT_BLKP(curr);
	}	

	return 1;	//all free blocks are in the segregated free list
}
*/


/*
* check if the successor and predecessor pointers in the free block actually point to valid heap addresses
*/
/*static int 
check_seg_list_ptrs() {
	int list_class = 0;
	void *curr;

	while (list_class < NUM_LISTS) {
		curr = (void *) seg_free_list[list_class];	//pointer to start of list-class
		if(curr != NULL) {
			if(curr < mem_heap_lo() || curr > mem_heap_hi() ) {	//check if the address is within header and footer
				printf("ERROR: address violation\n");
				return 0;
			}
		}

		list_class++;
	}

	return 1;	//all pointers point to valid heap addresses
}*/

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
/*static void
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
}*/

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
