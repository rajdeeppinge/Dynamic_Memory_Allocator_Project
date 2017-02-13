/*
 *name - omkar damle
 *id - 201401114	 
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
 *
 * segregated free lists approach used.  In that segregated fits approach implemented. LIFO ordering and a
 * first fit placement policy used in each of the individual free lists which are implemented as explicit lists.
 * boundary tag immediate coalescing used.
 * to be implemented for better performance:
 * 1. deferred coalescing	
 * 2. realloc can be optimised
 * 2.5 . address/size ordered instead of LIFO - explicit lists.		
 * 3. selective splitting - split only when saving is big enough
 * 4. use next fit instead of first fit
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
	"united",
	/* First member's full name */
	"omkar damle",
	/* First member's email address */
	"201401114@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"",
	/* Second member's email address (leave blank if none) */
	""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
//#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

/*
#define MAXSIZE_CLASS_0 (4 * WSIZE)
#define MAXSIZE_CLASS_1 (6 * WSIZE)
#define MAXSIZE_CLASS_2 (8 * WSIZE)
#define MAXSIZE_CLASS_3 (10 * WSIZE)
#define MAXSIZE_CLASS_4 (12 * WSIZE)
#define MAXSIZE_CLASS_5 (14 * WSIZE)
#define MAXSIZE_CLASS_6 (16 * WSIZE)
#define MAXSIZE_CLASS_7 (18 * WSIZE)
#define MAXSIZE_CLASS_8 (20 * WSIZE)
#define MAXSIZE_CLASS_9 (48 * WSIZE)
#define MAXSIZE_CLASS_10 (50 * WSIZE)
#define MAXSIZE_CLASS_11 (52 * WSIZE)
#define MAXSIZE_CLASS_12 (54 * WSIZE)
#define MAXSIZE_CLASS_13 (56 * WSIZE)
#define MAXSIZE_CLASS_14 (58 * WSIZE)
#define MAXSIZE_CLASS_15 (100 * WSIZE)
#define MAXSIZE_CLASS_16 ((1000000000000000000000000000000000000000) * WSIZE)			//check
*/


/*
#define MAXSIZE_CLASS_0 64
#define MAXSIZE_CLASS_1 128
#define MAXSIZE_CLASS_2 256
#define MAXSIZE_CLASS_3 512
#define MAXSIZE_CLASS_4 1024
#define MAXSIZE_CLASS_5 2048
#define MAXSIZE_CLASS_6 4096
#define MAXSIZE_CLASS_7 8192
#define MAXSIZE_CLASS_8 16384
#define MAXSIZE_CLASS_9 9999999	
*/


#define MAXSIZE_CLASS_0 (8 * WSIZE )
#define MAXSIZE_CLASS_1 (16 * WSIZE )
#define MAXSIZE_CLASS_2 (32 * WSIZE )
#define MAXSIZE_CLASS_3 (64 * WSIZE )
#define MAXSIZE_CLASS_4 (128 * WSIZE )
#define MAXSIZE_CLASS_5 (256 * WSIZE )
#define MAXSIZE_CLASS_6 (512 * WSIZE )
#define MAXSIZE_CLASS_7 (1024 * WSIZE )
#define MAXSIZE_CLASS_8 (2048 * WSIZE )
#define MAXSIZE_CLASS_9 (4096 * WSIZE )
/*
#define MAXSIZE_CLASS_10 (24 * WSIZE)
#define MAXSIZE_CLASS_11 (26 * WSIZE)
#define MAXSIZE_CLASS_12 (28 * WSIZE)
#define MAXSIZE_CLASS_13 (30 * WSIZE)
#define MAXSIZE_CLASS_14 (32 * WSIZE)
#define MAXSIZE_CLASS_15 (34 * WSIZE)
#define MAXSIZE_CLASS_16 (36 * WSIZE)
#define MAXSIZE_CLASS_17 (38 * WSIZE)
#define MAXSIZE_CLASS_18 (40 * WSIZE)
#define MAXSIZE_CLASS_19 (42 * WSIZE)
#define MAXSIZE_CLASS_20 (44 * WSIZE)
#define MAXSIZE_CLASS_21 (46 * WSIZE)
#define MAXSIZE_CLASS_22 (48 * WSIZE)
#define MAXSIZE_CLASS_23 (50 * WSIZE)
#define MAXSIZE_CLASS_24 (52 * WSIZE)
#define MAXSIZE_CLASS_25 (54 * WSIZE)
#define MAXSIZE_CLASS_26 (56 * WSIZE)
#define MAXSIZE_CLASS_27 (58 * WSIZE)
#define MAXSIZE_CLASS_28 (60 * WSIZE)
#define MAXSIZE_CLASS_29 (72 * WSIZE)
#define MAXSIZE_CLASS_30 (80 * WSIZE)
#define MAXSIZE_CLASS_31 (100 * WSIZE)
#define MAXSIZE_CLASS_32 (200 * WSIZE)
#define MAXSIZE_CLASS_33 (300 * WSIZE)
#define MAXSIZE_CLASS_34 ((1000000000000000000000000000000000000000) * WSIZE)			//check
*/

#define NO_SEG_CLASSES 10

#define REALLOC_BUFFER (1<<7)

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  
#define MIN(x, y)  ((x) < (y) ? (x) : (y))  


/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))
//#define PUT_WITH_TAG(p ,val) (*(uintptr_t *)(p) = (val) | GET_RATAG(p))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*for reallocation tags*/
//#define GET_RATAG(p) (GET(p) & 0x2)
//#define SET_RATAG(p) (GET(p) |= 0x2)
//#define REMOVE_RATAG(p) (GET(p) &= ~0x2)



/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
static char *next_fit_ptr ; /*next fit pointer..initialise to heap_listp*/
static unsigned int** segregation_classes;	/*used to keep reference of the segregation classes */

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
//static void *find_fit(size_t asize);
//static void place(void *bp, size_t asize);

/*functions defined exclusively for segregated list implementation*/
static void add_block_in_segregated_list(void* bp , int class);
static void remove_from_list(void* bp, int class);
//static void* find_fit_by_class(size_t asize , int class);
static void place_segregated_list(void* bp ,size_t asize);
static int get_class_from_size(size_t asize);
static int get_class(void* bp);
static size_t extra_realloc_size(size_t size);
static void* find_fit_by_class_pseudo_best_fit(size_t asize , int class);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:	
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 *   Note- we are using segregated free list. So we need to make some space for the pointers to the first item in each list i.e. an array 
 *   of pointers to the various segregation classes.
 */

int
mm_init(void) 
{

	int n  = NO_SEG_CLASSES; 					//no of segregation classes
	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE + n * WSIZE)) == (void *)-1)
		return (-1);

	segregation_classes = (unsigned int**) heap_listp;			//setting the array of pointers to free lists
	int i;

	for(i=0;i<n;i++)
		segregation_classes[i] = NULL;				//inititalise all pointers to be null
				
  	heap_listp = (char *)(&segregation_classes[n-1] + 1);		
							//now the alignment padding and prologue and epilogue come into picture 

	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);
	next_fit_ptr = heap_listp;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/*
 * This function is used to remove a block from its segregated free list class as it is going to be allocated.
 */

void remove_from_list(void* bp, int class)	//note bp points to word after header
{
unsigned int** prev = (unsigned int**)(*((unsigned int**)bp));
unsigned int** next = (unsigned int**)(* ((unsigned int**)bp + 1));


//asssumption prev and next point to word after header of prev/next block
if(prev != NULL)
	{
		*(prev + 1) = (unsigned int*)next;
	}
else
	{//as the block being removed is the header, we need to initialise the header to next block
		segregation_classes[class] = (unsigned int*)next;	
	}

if(next != NULL)
	{
		
		*(next) = (unsigned int*)prev;
	}
else
	{//as the block being removed is the last one in the list, we don't need to do anything	
	}
}

/*
 * This function is used to add a block to its segregated free list class. The block is added to the beginning of the list.
 */


void add_block_in_segregated_list(void* bp , int class)
{
*((unsigned int**)bp) = NULL ;  					//since its the first in the list, its prev field is made NULL.
*((unsigned int**)bp + 1) = (unsigned int*) segregation_classes[class];	// next field is initialised.
	
//assumption : segregation classes contain pointer to word after header.
if(segregation_classes[class] != NULL)
	{
	*((unsigned int**)segregation_classes[class]) = (unsigned int*)bp;		//prev field of the earlier first member is initialised.
	}
else
	{
	// do nothing if list was empty inititally.
	}

segregation_classes[class] = (unsigned int*)bp;

}

/*given a free block return its class
*/

static int get_class(void* bp)
{
	size_t asize = GET_SIZE(HDRP(bp));
	return get_class_from_size(asize);
}

/*
given size of block return its class
*/
static int get_class_from_size(size_t asize)
{
	int i;

	if(asize<= MAXSIZE_CLASS_0)
		i=0;
	else if(asize<= MAXSIZE_CLASS_1)
		i=1;
	else if(asize<= MAXSIZE_CLASS_2)
		i=2;
	else if(asize<= MAXSIZE_CLASS_3)
		i=3;
	else if(asize<= MAXSIZE_CLASS_4)
		i=4;
	else if(asize<= MAXSIZE_CLASS_5)
		i=5;
	else if(asize<= MAXSIZE_CLASS_6)
		i=6;
	else if(asize<= MAXSIZE_CLASS_7)
		i=7;
	else if(asize<= MAXSIZE_CLASS_8)
		i=8;
	else 					//if(asize<= MAXSIZE_CLASS_9)
		i=9;
	/*else if(asize<= MAXSIZE_CLASS_10)
		i=10;
	else if(asize<= MAXSIZE_CLASS_11)
		i=11;
	else if(asize<= MAXSIZE_CLASS_12)
		i=12;
	else if(asize<= MAXSIZE_CLASS_13)
		i=13;
	else if(asize<= MAXSIZE_CLASS_14)
		i=14;
	else if(asize<= MAXSIZE_CLASS_15)
		i=15;
	else if(asize<= MAXSIZE_CLASS_16)
		i=16;
	else if(asize<= MAXSIZE_CLASS_17)
		i=17;
	else if(asize<= MAXSIZE_CLASS_18)
		i=18;
	else if(asize<= MAXSIZE_CLASS_19)
		i=19;
	else if(asize<= MAXSIZE_CLASS_20)
		i=20;
	else if(asize<= MAXSIZE_CLASS_21)
		i=21;
	else if(asize<= MAXSIZE_CLASS_22)
		i=22;
	else if(asize<= MAXSIZE_CLASS_23)
		i=23;
	else if(asize<= MAXSIZE_CLASS_24) 
		i=24;
	else if(asize<= MAXSIZE_CLASS_25)
		i=25;
	else if(asize<= MAXSIZE_CLASS_26)
		i=26;
	else if(asize<= MAXSIZE_CLASS_27)
		i=27;
	else if(asize<= MAXSIZE_CLASS_28)
		i=28;
	else if(asize<= MAXSIZE_CLASS_29)
		i=29;
	else if(asize<= MAXSIZE_CLASS_30)
		i=30;
	else if(asize<= MAXSIZE_CLASS_31)
		i=31;
	else if(asize<= MAXSIZE_CLASS_32)
		i=32;
	else if(asize<= MAXSIZE_CLASS_33)
		i=33;
	else 
		i=34;	
	*/
return i;
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
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);				/*can be further optimized for 64 bit M/Cs 													where only 8 byte alignment is required*/  

	/* let us find the segregated class which fits this allocation request */

	int i= get_class_from_size(asize);

	for(; i<=NO_SEG_CLASSES - 1 ; i++)
		{
		bp = find_fit_by_class_pseudo_best_fit(asize , i);
					
		if(bp!=NULL)
			{
			// function for removing 'to be allocated' block from segregated free list. 
			remove_from_list(bp,i);			
			place_segregated_list(bp ,asize);			
			return bp;
			}		
		}



/*
	 Search the free list for a fit. 
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}
*/


/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	remove_from_list(bp, get_class(bp));
	place_segregated_list(bp , asize);
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
	
	//REMOVE_RATAG(HDRP(NEXT_BLKP(bp))); 			//??	
	//PUT_WITH_TAG(HDRP(bp), PACK(size, 0));
	//PUT_WITH_TAG(FTRP(bp), PACK(size, 0));
	

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
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
void *
mm_realloc(void *ptr, size_t size)
{
	//size_t oldsize;
	//void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	//If the realloc'd block has previously been given more size than it needs, then
   	//this realloc request may be serviced within the same block. This will save us time.

	size_t currSize = GET_SIZE(HDRP(ptr));
	if(size < currSize - 2*WSIZE)			//because size given in realloc request doesnt contain the header and footer
			return ptr;
	
	void* next = NEXT_BLKP(ptr);
	int next_alloc = GET_ALLOC(HDRP(next));		//check if next block is free.

	size_t coalesce_size = GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr));	
	
	if(!next_alloc && size < coalesce_size - 2*WSIZE)
		{
		remove_from_list(next, get_class(next));
		PUT(HDRP(ptr) , PACK(coalesce_size , 1));
		PUT(FTRP(ptr) , PACK(coalesce_size , 1));
		return ptr;
	}

	//now if we cant realloc in place, then we need to malloc. While mallocing make sure you keep some extra space at the end of the block
	//so that if a new reallocation request comes, it can be handled in place.
	size_t newSize = extra_realloc_size(size);	
	

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(newSize));

	void* oldptr = ptr;
	void* newptr ;
	size_t copySize ;

	newptr = mm_malloc(newSize);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	copySize = GET_SIZE(HDRP(oldptr));
	
	if (size < copySize)
		copySize = size;
	memcpy(newptr, oldptr, copySize);

	/* Free the old block. */
	mm_free(oldptr);

	return (newptr);
}

static size_t extra_realloc_size(size_t size)
{
    size_t biggerBuffer = size * 16;			//was initially 4 
    //Assuming one would want to realloc into a size class somewhat more than twice the previous size.
    //This is in line with common use cases such as extending an array (e.g. C++ vectors)

    //But we will clamp that extra amount in multiples of page size
    if (biggerBuffer > size + 24576) { //currently at 6 pages
        biggerBuffer = size + 24576;							//???????
    }

    return biggerBuffer;

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
 *   block. Also it needs to add the blocks in appropriate free lists.
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	int class = get_class(bp);

	// Do not coalesce with prev block if prev block is tagged with reallocation tag. 		//??
	//if(GET_RATAG(HDRP(PREV_BLKP(bp))))
	//	prev_alloc = 1 ;  

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		add_block_in_segregated_list(bp , class);		
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		remove_from_list( NEXT_BLKP(bp), get_class(NEXT_BLKP(bp)));	
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		//PUT_WITH_TAG(HDRP(bp), PACK(size, 0));
		//PUT_WITH_TAG(FTRP(bp), PACK(size, 0));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

		add_block_in_segregated_list(bp , get_class(bp));		//class may be changed
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		remove_from_list( PREV_BLKP(bp), get_class(PREV_BLKP(bp)));		
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		//PUT_WITH_TAG(FTRP(bp), PACK(size, 0));
		//PUT_WITH_TAG(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		add_block_in_segregated_list(bp , get_class(bp));		//class may be changed
	} else {                                        /* Case 4 */
		remove_from_list( NEXT_BLKP(bp), get_class(NEXT_BLKP(bp)));	
		remove_from_list( PREV_BLKP(bp), get_class(PREV_BLKP(bp)));		
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		//PUT_WITH_TAG(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		//PUT_WITH_TAG(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		

		bp = PREV_BLKP(bp);
		add_block_in_segregated_list(bp , get_class(bp));		//class may be changed
	}

	//note that bp is changing in some else statements..but our code works for those cases too	
/*	if(next_fit_ptr > PREV_BLKP(bp) && next_fit_ptr < NEXT_BLKP(bp))
		{
		next_fit_ptr = PREV_BLKP(bp);
		}
*/
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
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */			//??

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

/*
static void *
find_fit(size_t asize)
{
	void *bp;

	// Search for the first fit. 
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))			//if block is free and size of block is more than or equal to required size,
			return (bp);
	}
	// No fit was found. 
	return (NULL);
}
*/

//this is best fit
/*
static void* find_fit(size_t asize)
{

int flag=0 ;		// if flag remains 0, no space found 
void *bp ,*best_fit_ptr ;
size_t min_padding = 1000000000,padding;

for(bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
	if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
		{
		padding = GET_SIZE(HDRP(bp)) - asize ; 
		if(padding < min_padding)	
			{
			min_padding = padding;
			best_fit_ptr = bp;	
			flag = 1;
			}
		}
}

if(flag == 0)
	return NULL;
else
	return best_fit_ptr;

}
*/




/*
//this is next fit
static void* find_fit(size_t asize)

{
void *bp ;
//size_t min_padding = 1000000000,padding;

for(bp = next_fit_ptr ; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
                {next_fit_ptr = bp;
		return bp;                                    
		}
}

//if we reach this point we have searched the later part
//let us search from beginning

for(bp = heap_listp ; bp != next_fit_ptr ; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
                {next_fit_ptr = bp;
		return bp;
		}
}

return NULL;
}
*/



/*
// This function is used in segregated free list implementation. We search the class for a first fit.


static void* find_fit_by_class(size_t asize , int class)
{
//curr points to the word after header of current block
unsigned int** curr = (unsigned int**)segregation_classes[class] ;		
//segregation classes array pointers point to the word following the header of first item in list.

while(curr!=NULL)
	{
	//if (asize <= GET_SIZE(HDRP(curr)) && GET_RATAG(HDRP(curr)) == 0)//if size of free block is more than or equal to required size and 										//RATAG is not set
	if (asize <= GET_SIZE(HDRP(curr)))		
		return (curr);					//since we return bp
	
	curr = (unsigned int**)(*(curr + 1)) ;
							// move on to the next free block in same class	
	}	
		
//we have finished searching the given class but did not find any appropriate free block.
return NULL;
}
*/

static void* find_fit_by_class_pseudo_best_fit(size_t asize , int class)
{

//curr points to the word after header of current block
unsigned int** curr = (unsigned int**)segregation_classes[class] ;		
//segregation classes array pointers point to the word following the header of first item in list.

size_t min_padding = 999999999, padding;
unsigned int** best = NULL ;
int count = 0 , max_suitable = 5;		//max no of suitable blocks checked in pseudo best fit is 5 

while(curr!=NULL)
	{
	if (asize <= GET_SIZE(HDRP(curr)))		
		{							// 'suitable' block
		if(count > max_suitable)
			return (best);

		padding = GET_SIZE(HDRP(curr)) - asize ;

		if(padding < min_padding )		
			{min_padding = padding;		
			best = curr;			
			}
		count++ ;
							//since we return bp
		}
	curr = (unsigned int**)(*(curr + 1)) ;
							// move on to the next free block in same class	
	}	
		
//we have finished searching the given class but did not find any appropriate free block.
return best;

}


/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 *DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

*/


/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. The splitted block fragment is added to the appropriate segregation class 
 */
static void place_segregated_list(void* bp ,size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 *DSIZE)) { 
		//PUT_WITH_TAG(HDRP(bp), PACK(asize, 1));
		//PUT_WITH_TAG(FTRP(bp), PACK(asize, 1));
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));			/*we need to put the fragment in appropriate class*/
		PUT(FTRP(bp), PACK(csize - asize, 0));
		
		size_t free_block_size = csize - asize;		
		int i;

	i = get_class_from_size(free_block_size);	

	// add fragment in segregated class		

	add_block_in_segregated_list(bp , i);

	} else {
		//PUT_WITH_TAG(HDRP(bp), PACK(csize, 1));			//only PUT will also do
		//PUT_WITH_TAG(FTRP(bp), PACK(csize, 1));
		PUT(HDRP(bp), PACK(csize, 1));			//only PUT will also do
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
