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
#include <math.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"MALICIOUS MALLOCS",
	/* First member's full name */
	"Emily Hook",
	/* First member's NetID */
	"eeh6",
	/* Second member's full name (leave blank if none) */
	"Samuel Cheng",
	/* Second member's NetID (leave blank if none) */
	"sc83"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */
#define BUCKET(p)  (unsigned int) (pow(2, p + 4))

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

/*
 * A free list block:
 *
 *  Stores the prev/next pointers to point to respective free blocks. 
 */
struct free_block {
	/* 
	 *The pointer to the previous element in the explicit free list.
	 */
	struct free_block *prev; 
	
	/*
	 * The pointer to the next element in the explicit free list.
	 */
	struct free_block *next; 
};

/* Global variables: */
static struct free_block **free_listp; /* Pointer to free list array */ 
static char *heap_listp; /* Pointer to first block after free list array */ 
static size_t failedsize; /* Last size that needed heap extension */ 

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words); 
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize, bool remove_flag);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/*
 * The following are team defined helper functions.
 */

/* 
 * Requires:
 * "size" is the needed size for the malloc allocation.
 *
 * Effects:
 *   Find the appropriate free linked list for a block of this size.  
 *    Returns the index of the pointer array that contains the
 *    pointer to this list.
 */
int
find_list(size_t size)
{	

	if (size <= 64) {
		return 0;
	} else if (size <= 128) {
		return 1;
	} else if (size <= 256) {
		return 2;
	} else if (size <= 512) {
		return 3;
	} else if (size <= 1024) {
		return 4;
	} else if (size <= 2048) {
		return 5;
	} else if (size <= 4096) {
		return 6;
	} else {
		return 7;
	}   
};

/*
 * Requires:
 * 	 "bp" is the address of a free block that is at least "asize" bytes. 
 *
 * Effects:
 *   Inserts the block pointed to by bp into the front of
 *    the appropriate free linked list for a block of this size.  
 *    
 */
void
insert_free(size_t asize, void *bp) 
{
        struct free_block *first;
        int idx = find_list(asize); 
	/* 
	 *  If the explicit free list is empty, set the block 
	 *  as the one node of the list. Else, insert block at start 
	 *  of appropriately sized explicit free list and link it to the 
	 *  rest of the list. 
	 */
    if (free_listp[idx] == NULL) {
	        free_listp[idx] = (struct free_block *) bp;
			free_listp[idx]->next = NULL;
	        free_listp[idx]->prev = NULL;
        } else {
	        first = (struct free_block *) bp;
            first->next = free_listp[idx];
	        first->prev = NULL;
			free_listp[idx]->prev = first;
	        free_listp[idx] = first;	
	}
}

/*
 * Requires:
 *   "bp" is the address of a free block to be removed. 
 *
 * Effects:
 *   Removes the block pointed to by bp from the free list
 *    of which it is a member, either having been given the 
 *     index or having calculated it using the block size.  
 *    
 */

void
remove_free(void *bp) 
{

	size_t size = GET_SIZE(HDRP(bp));
	int list = find_list(size);
	struct free_block *current = (struct free_block *) bp;

	/* 
	 *  If the block is at the start of the list, either make the 
	 *  next block the first node of the list, or if it was the only 
	 *  block in the list, set the explicit free list to NULL.
	 */
	if (current->prev == NULL) {
		if (current->next != NULL) {
			current->next->prev = NULL;	
			free_listp[list] = current->next;	
			return;
		} else {
			free_listp[list] = NULL;
			return;
		}
	}
 	/* 
	 *  If the block is at the end of the list, make the second to last 
	 *  block point to NULL. Else, the block is in the middle, so link the
	 *  prev and next to each other. 
	 */
	else if (current->next == NULL) {
		current->prev->next = NULL;
	} else {
		current->prev->next = current->next;
		current->next->prev = current->prev;
			return;
	}
}

/* 
* End of helper function section.
*/

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

	void *startp;
	int i; 

	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	if ((startp = mem_sbrk(10 * sizeof(struct free_block *) )) == (void *)-1)
		return (-1);
	
	// Set the header and footer, as well an extended epilogue header. 
	PUT(HDRP(startp), PACK(10 * WSIZE , 1));
	PUT(FTRP(startp), PACK(10 * WSIZE , 1));
	PUT(NEXT_BLKP(startp), PACK(0, 1));     /* Epilogue header */

	// Initialize all free lists to null. 
	struct free_block *first_list = (struct free_block *) startp;
	free_listp = (struct free_block **) first_list;
	for (i = 0; i < 8; i++) {
		free_listp[i] = NULL;
	}
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

	/*
 	*  Optimization trick. If the last malloc request found no fit and 
	*  this current one asks for the same size, just skip to extending the
	*  heap - there is still no free block large enough for it. 
 	*/
	if (asize == failedsize) {
		if ((bp = extend_heap(asize / WSIZE)) == NULL) {
			return (NULL);
		}
		place(bp, asize, 0);
		return (bp);
	}

	/* Search the free lists for a fit and place into the free block. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize, 1);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = asize;
	failedsize = asize;
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
		return (NULL);
	}
	place(bp, asize, 0);
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

	size = GET_SIZE(HDRP(bp));
	
	/* For optimization. If we have a new freed chunk equal to the size
	* of the last size that required extension, we no longer need 
	* auto-extension in malloc. 
	*/ 
	if (size == failedsize) {
		failedsize = 0;
	}

	// Set the allocation flags of the block to free! 
	// Coalesce the newly freed block. 
    PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp); 
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 * 	 "size" is the new size you need for the allocated block pointed 
 *    to by "ptr". 
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
	size_t oldsize;
	size_t asize;
	void *newptr = NULL;
	
	oldsize = GET_SIZE(HDRP(ptr));

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL) {
		return (mm_malloc(size));
	// If not, we're going to (maybe) look for a new home for our block. 
	} else { 
		// If we are looking for a smaller size, return same block.
		if (asize <= oldsize) {
			// Made payload smaller, take internal fragmentation
			return ptr;
		// If we are looking for a larger block, extend heap or relocate.
		} else if (GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0) {

					extend_heap((asize - oldsize) / WSIZE);
					PUT(HDRP(ptr), PACK(asize, 1));
					PUT(FTRP(ptr), PACK(asize, 1));
					return ptr;
		} else {
				newptr = mm_malloc(size);
				memcpy(newptr, ptr, oldsize);
				mm_free(ptr);
				return (newptr);
		}
	}
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
	bool prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));  
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 

	if (prev_alloc && next_alloc) {                 /* Case 1 */
	  	insert_free(size, bp);
		return (bp);
	} else if (prev_alloc && !next_alloc) {        /* Case 2 */  
		remove_free(NEXT_BLKP(bp));

		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		
		insert_free(size, bp);
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		remove_free(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);

		insert_free(size, bp);

	} else {                                        /* Case 4 */
		remove_free(NEXT_BLKP(bp));
		remove_free(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	
		bp = PREV_BLKP(bp);
		insert_free(size, bp);	
	}
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

	return bp;
}

/*
 * Requires:
 *   "asize" is the aligned size malloc needs to find a free block for. 
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{

    struct free_block *current;
	int idx = find_list(asize);

	/* Loop through the free lists to find a free list with an appropriate free block. */
	while (idx < 8) {
		for (current = free_listp[idx]; current !=  NULL; current = current->next) {
			if (GET_SIZE(HDRP(current)) >= asize) 
				return((void *)current);
		}
		idx++;     
	}
	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 * 	 "remove_flag" is an indicator of whether or not to remove the block.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize, bool remove_flag)
{

	size_t csize = GET_SIZE(HDRP(bp)); 

	if (remove_flag)
		remove_free(bp);

	if ((csize - asize) >= (2 * DSIZE)) { 

		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		insert_free((csize - asize), bp);

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

	if ((uintptr_t)bp % WSIZE)
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

	if (GET_SIZE(HDRP(heap_listp)) != WSIZE ||
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