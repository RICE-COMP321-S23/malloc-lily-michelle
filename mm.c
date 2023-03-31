/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
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
	"Machine Learning",
	/* First member's full name */
	"Michelle Pang",
	/* First member's NetID */
	"yp29",
	/* Second member's full name (leave blank if none) */
	"Lily Gao",
	/* Second member's NetID (leave blank if none) */
	"qg8"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define ALIGN_SIZE 8		  /* Alignment size */
#define SEGSIZE    10             /* Free list segregation */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(ALIGN_SIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Struct for segregated free list. */
struct block_list
{
	struct block_list *next_list; /* Pointer to next block list */
	struct block_list *prev_list; /* Pointer to previous block list */
};

/* Global variables: */
static char *heap_listp; /* Pointer to first block. */  

/* Pointer to first block_list of free list. */
struct block_list *seg_first; 

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* Helper functions: */
static void list_remove(struct block_list *bp);
static void list_insert(struct block_list *bp, size_t size);
static int seg_index(size_t size);
static size_t next_power_of_2(size_t n);

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
	/* Initialize memory for storing the free list in the heap. */
	if ((seg_first = mem_sbrk(2 * SEGSIZE * sizeof(void*))) == (void *)-1)
		return (-1);

	/* Initialize seg_first. */
	int i;	
	for (i = 0; i < SEGSIZE; i++) {
		seg_first[i].next_list = &seg_first[i];
		seg_first[i].prev_list = &seg_first[i];
	}

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += 2 * WSIZE;
	
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
	
	/* Make sure size is large enough, avoid fragmentation. */
	if (size <= 16 * DSIZE)
		size = next_power_of_2(size);
		
	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = ALIGN_SIZE * 
		    ((size + DSIZE + (ALIGN_SIZE - 1)) / ALIGN_SIZE);

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
	size_t oldsize, asize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));
	
	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = ALIGN_SIZE * 
		    ((size + DSIZE + (ALIGN_SIZE - 1)) / ALIGN_SIZE);
	
	/* Copy just the old data, not the old header and footer. */
	oldsize = GET_SIZE(HDRP(ptr)) - DSIZE;
	if (asize < oldsize + DSIZE) 
		return (ptr);
	if (size < oldsize)
		oldsize = size;

	newptr = mm_malloc(SEGSIZE * size);

	/* If realloc() fails, the original block is left untouched.  */
	if (newptr == NULL)
		return (NULL);

	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
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
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		/* Bp stays same. */
		bp = bp;	
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

		/* Remove next. */
		list_remove((struct block_list *)NEXT_BLKP(bp));

		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		/* Remove prev. */
		list_remove((struct block_list *)PREV_BLKP(bp)); 

		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));

		/* Remove prev and next. */
		list_remove((struct block_list *)PREV_BLKP(bp));
		list_remove((struct block_list *)NEXT_BLKP(bp));

		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	/* Insert corresponding bp. */
	list_insert(bp, size);
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
	size_t size;
	void *bp;

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
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	
	struct block_list *bp; 

	/* Search for the first fit. */
	for (int i = seg_index(asize); i < SEGSIZE; i++) {
		
		/* Search for fit from every index of seg_first. */
		for (bp = seg_first[i].next_list; bp && bp != &seg_first[i]; 
		    bp = bp->next_list) {
			if (asize <= GET_SIZE(HDRP(bp)))
				return (void*)bp;
		}
	}
	/* No fit was found. */
	return (NULL);
	
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
	list_remove(bp);
	if ((csize - asize) >= (2 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));

		/* Place block after removal.*/
		list_insert(bp, csize - asize);
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
 *   Perform a check on the block "bp".
 */
static void
checkblock(void *bp) 
{	
	/* Check if the pointer is doubleword aligned. */
	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned!\n", bp);

	/* Check if the header matches with footer. */
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer!\n");

	int index = seg_index(GET_SIZE(HDRP(bp)));
	struct block_list *i = seg_first;
	if (!GET_ALLOC(HDRP(bp))) {
		/* Check if free blocks are in the correct free list. */
		while (i != NULL) {
			if (i == bp) {
				printf("Found %p in free list index %u\n", 
				    bp, index);
				return;
			}
			i = i->next_list;
		}
		printf("Error: %p not in free ist at index %u at size %zu \n", 
		    bp, index, GET_SIZE(HDRP(bp)));
	} else {
		/* Check that non free blocks aren't in any free lists. */
		while (i != NULL) {
			if (i == bp) {
				printf("Found non-free block %p", bp);
				return;
			}
			if (i == NULL || i->next_list == NULL) {
				break;
			}
			i = i->next_list;
		}
	}
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{	
	void *bp;
	char* current;
	char* next;
        char* start;
	current = heap_listp;
	start = heap_listp;
	next = NEXT_BLKP(start);
	size_t hsize, halloc, fsize, falloc;
   	hsize = GET_SIZE(HDRP(bp));
    	halloc = GET_ALLOC(HDRP(bp));
    	fsize = GET_SIZE(FTRP(bp));
    	falloc = GET_ALLOC(FTRP(bp));

	// Check if any contiguous free blocks that somehow escaped coalescing.

	while (start != next) {
		if (GET_ALLOC(current) && !GET_ALLOC(next)) 
			printf("Ajacent blocks are free and uncoalesced! \n");
		current = next;
		next = NEXT_BLKP(next);
	}

	/* 
	 * Checks if the header and footer of a block given as input is 
	 * consistent. Runs silently unless there is a mismatch between 
	 * header and footer.
	 */
    	if(hsize!=fsize ||(falloc!=halloc))
        	printf("\n Inconsistent header & footer. Recheck block %p\n",
		    bp);
	
	if (verbose) {
		printf("\n----New Checkheap----\n");
		printf("Heap (%p):\n", heap_listp);
	}

	// Check prologue.
	if (GET_SIZE(HDRP(heap_listp)) != DSIZE || 
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header!\n");
	checkblock(heap_listp);

	// Check epilogue.
	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header!\n");
	
	// Check if every block in the free list marked as free.
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	/*
	 * Check if every free block actually in the free list.
	 * Print entire free list.
	 */ 
	if (verbose) {
		struct block_list *head = seg_first;
		for (struct block_list *head = seg_first; 
		    head != NULL; head = head->next_list) {
			printf("Mistake here on %p", head);
			return;
		}
		printf("Block %p in free list index", head);
		printf(" %zu with allocation",GET_SIZE(HDRP(head)));
		printf(" %c\n", GET_ALLOC(HDRP(head)) ? 'a' : 'f');
	}
		
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
	size_t hsize, fsize;
	bool halloc, falloc;

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
 * Requires:
 *   "size" is the size bytes to locate index of seg_first.
 *
 * Effects:
 *   Returns the index of seg_first.
 */
inline static int 
seg_index(size_t size) 
{
	/* Depending on size, locate index 0-9. */
	if (size <= 32) 			
		return 0;
	else if (size <= 64) 	
		return 1;
	else if (size <= 128) 	
		return 2;
	else if (size <= 256) 	
		return 3;
	else if (size <= 512) 	
		return 4;
	else if (size <= 1024) 	
		return 5;
	else if (size <= 2048) 	
		return 6;
	else if (size <= 4096) 	
		return 7;
	else if (size <= 8192) 	
		return 8;
	else  						
		return 9;
	
}

/* 
 * Requires:
 *    "bp" is the address of inserted block, "size" is the size bytes used to 
 *    locate index using seg_index function.
 * 
 * Effects:
 *    Insert "bp" to corresponding place in seg_first.
 */
inline static void
list_insert(struct block_list *bp, size_t size)
{
	/* Get the supposed previous and next block_list of bp. */
	struct block_list *start = &seg_first[seg_index(size)];
	struct block_list *new_after = start->next_list;

	/* Perform bp insertion. */
	bp->prev_list = start;
	bp->next_list = new_after;
	new_after->prev_list = bp;
	start->next_list = bp;
}

/* 
 * Requires:
 *    "bp" is the address of removed block.
 * 
 * Effects:
 *    Remove "bp" from seg_first.
 */
inline static void
list_remove(struct block_list *bp)
{
	/* Get the previous and next block_list of bp. */
	struct block_list *new_prev = bp->prev_list;
	struct block_list *new_next = bp->next_list;

	/* Perform bp removal. */
	new_prev->next_list = new_next;
	new_next->prev_list = new_prev;
	
}

/*
 * Requires:
 *   "size" is a size bytes.
 *
 * Effects:
 *   Returns next largest power of 2 of "size".
 */
inline static size_t
next_power_of_2(size_t n)
{
	/* Divide by 2 consecutively doubling up to 32. */
	n--;
	n |= n >> 1;   
	n |= n >> 2;   
	n |= n >> 4;
	n |= n >> 8;
	n |= n >> 16;

	/* Final 1 bit shift. */
	n++;           
	return (n);
}