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
	"sc80"
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
	 * uintptr_t *header; (***DON'T NEED THESE BECAUSE MACROS***)
	 * uintptr_t *footer;
	 */
	
	/* 
	 *The pointer to the previous element in the same explicit free list.
	 */
	struct free_block *prev; 
	
	/*
	 * The pointer to the next element in the same explicit free list.
	 */
	struct free_block *next; 
};

/*
 * A doubly linked list for the different bucket sizes:
 *
 *  Stores the pointer to the first free block in this bucket size's 
 *  corresponding free list, the prev/next pointers to point to respective 
 *  bucket lists, and the power to which two is raised to create this bucket size 
 * 
 * struct bucket_block {
       int power; 
        struct free_block *first_block;
        **USE GLOBAL VARS INSTEAD**
        struct bucket_block *prev;
        struct bucket_block *next;
  };
*/

/* Global variables: */
static struct free_block **free_listp; /* Pointer to free list array */ 
static        char       *heap_listp; /* Pointer to first block after free list array */ 


  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words); 
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/*
 * The following are team defined helper functions
 */

/* 
 * Requires:
 *   Size of a block 
 *
 * Effects:
 *   Find the appropriate free linked list for a block of this size.  
 *    Returns the index of the pointer array that contains the
 *    pointer to this list
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
 *   Size of a block, block pointer *bp 
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
	//printf("called insert on block of size = %d, index = %d \n", idx, (int) asize);
	/* 
	 *  Insert block at start of  appropriately sized explicit 
	 *  free list 
	 */
    if (free_listp[idx] == NULL) {
	        free_listp[idx] = (struct free_block *) bp;
			free_listp[idx]->next = NULL;
	        free_listp[idx]->prev = NULL;
			// printf("Inserted into empty list at index %d \n", idx);

        } else {
	        first = (struct free_block *) bp;
            first->next = free_listp[idx];
	        first->prev = NULL;
			free_listp[idx]->prev = first;
	        free_listp[idx] = first;	
			// printf("Inserted into non-empty list at index %d \n", idx);
       
	}
        //printf("inserted block of size = %d \n", (int) asize);
}

/*
 * Requires:
 *   Size of a block, pointer to free block *bp 
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
//   printf("called remove \n");

	size_t size = GET_SIZE(HDRP(bp));
	int list = find_list(size);
	struct free_block *current = (struct free_block *) bp;

	// printf("block to be removed size: %i", (int) GET_SIZE(HDRP(current)));
	// printf("block to be removed list: %i", (int) find_list(GET_SIZE(HDRP(current)), 0));

	// If block is at front of free list. 
	if (current->prev == NULL) {
		// printf("front\n");
		if (current->next != NULL) {
			current->next->prev = NULL;	
			free_listp[list] = current->next;	
			return;
		} else {
			free_listp[list] = NULL;
			return;
		}
	}
 /* free block was at the end of its 
			   * free list */
	else if (current->next == NULL) {
		// printf("back\n");
		current->prev->next = NULL;
	} else {
		// printf("mid\n");
		current->prev->next = current->next;
		current->next->prev = current->prev;
		//current = NULL;
			return;
			}
		}
	



/* 
* End of helper function section
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
	// printf("START______________________\n");
		/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	
	void *startp;
    if ((startp = mem_sbrk(10 * sizeof(struct free_block *) )) == (void *)-1)
		return (-1);
	
	// set header and footer 
	PUT(HDRP(startp), PACK(10 * WSIZE , 1));
	PUT(FTRP(startp), PACK(10 * WSIZE , 1));
	PUT(NEXT_BLKP(startp), PACK(0, 1));     /* Epilogue header */

	struct free_block *first_list = (struct free_block *) startp;
	free_listp = (struct free_block **) first_list;
	int i; 
	for (i = 0; i < 8; i++) {
		free_listp[i] = NULL;
	}
	
	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	// if (extend_heap(CHUNKSIZE / WSIZE)  == NULL)
	// 	return (-1);
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

	//printf("called malloc on block of size %d \n", (int) asize);
	/* Search the free list for a fit. */
	// printf("Need Size: %i\n",(int) asize);

	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		// printf("malloced pointer %p, %i \n", bp, (int) asize);
		return (bp);
	}

	// printf("ends up here? \n");
	/* No fit found.  Get more memory and place the block. */
	extendsize = asize;
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
		return (NULL);
	}
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
	//struct free_block *first;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free the block. */
	size = GET_SIZE(HDRP(bp));
	// printf("called free %p, %i\n", bp, (int) size);

	// insert_free(size, bp);
    PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp); //***?????
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
	// size_t expandsize;
	size_t oldsize;
	void *newptr;
	// struct free_block *current;

	newptr = ptr;
	oldsize = GET_SIZE(HDRP(ptr));
	// expandsize = oldsize;

	printf("size: %i\n", (int) size);
	printf("oldsize: %i\n", (int) oldsize);
	printf("pointer: %p", ptr);

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL) {
		return (mm_malloc(size));
	// If not, we're going to look for a (opt) new home for our block. 
	} else { 
		// If we are looking for a smaller size, split or stay.
		if (size <= oldsize) {
			void *next_ptr;
			printf("smaller unit");
			// Made payload smaller, take internal fragmentation
			PUT(HDRP(ptr), PACK(size, 1));
			PUT(FTRP(ptr), PACK(size, 1));
			if ((oldsize - size) >= (2 * DSIZE)) {
				next_ptr = NEXT_BLKP(ptr);
				insert_free((oldsize - size), next_ptr);
				
				PUT(HDRP(next_ptr), PACK(oldsize - size, 0));
				PUT(FTRP(next_ptr), PACK(oldsize - size, 0));
			}
			
		// If we are looking for a larger block, expand or relocate.
		} else {
			// current = ptr;
			// while (current->next != NULL) {
			// 	expandsize += GET_SIZE(HDRP(current)); 
			// 	if (expandsize >= size) {
			// 		PUT(HDRP(ptr), PACK(size, 1));
			// 		PUT(FTRP(ptr), PACK(size, 1));
			// 	}
			// }
			printf("larger unit\n");

			if (NEXT_BLKP(ptr) != NULL && !GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) {
				printf("getting here\n");
				printf("combined size %i\n", (int) (oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr)))));

				if (oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))) >= size) {
					printf("combined size %i", (int) (oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr)))));
					PUT(HDRP(ptr), PACK(size, 1));
					PUT(FTRP(ptr), PACK(size, 1));
				} 
			} else {
				printf("need to move\n");
				newptr = mm_malloc(size);
				if (size < oldsize)
					oldsize = size;
				memcpy(newptr, ptr, oldsize);
				mm_free(ptr);
				printf("new pointer! %p\n", newptr);
				return (newptr);

			}
			
		}

	}
return (newptr);
	

	// newptr = mm_malloc(size);

	// /* If realloc() fails the original block is left untouched  */
	// if (newptr == NULL)
	// 	return (NULL);

	// /* Copy the old data. */
	// oldsize = GET_SIZE(HDRP(ptr));
	// if (size < oldsize)
	// 	oldsize = size;
	// memcpy(newptr, ptr, oldsize);

	// /* Free the old block. */
	// mm_free(ptr);

	// return (newptr);
};

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
		//   printf("case 3 \n");
		remove_free(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		// If the size of the coalesced unit worth coalescing, coalesce and reassign


			PUT(FTRP(bp), PACK(size, 0));
			PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
			bp = PREV_BLKP(bp);

			insert_free(size, bp);

	} else {                                        /* Case 4 */
		//   printf("case 4 \n");
			remove_free(NEXT_BLKP(bp));
			remove_free(PREV_BLKP(bp));
			size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
			
			PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
			PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		

			bp = PREV_BLKP(bp);
			insert_free(size, bp);
		
	}
		//printf("finished coalescing [sucessful] \n");
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
	//struct free_block *first;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);
	// printf("extending with block of size %d \n", (int) size);
	/* Initialize free block header/footer and the epilogue header. */
 	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return coalesce(bp);
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
  //printf("called find fit on block of size %d \n", (int) asize);
  //void *bp;
    struct free_block *current;
	// printf("FIND FIT\n");
	int idx = find_list(asize);

	// What if a free list is empty? 
	// if (free_listp[idx] == NULL) {
	// 	return ;
	// }

	/* Search for the first fit. */
	while (idx < 8) {
	        for (current = free_listp[idx]; current !=  NULL; current = current->next) {
		        unsigned int bp_size = GET_SIZE(HDRP(current));
				// printf("searching list at index = %d, current block size = %d, current block = %p  \n", idx, bp_size, current);
		        if (bp_size >= asize) {
			  //bp = &current; //???
			//   printf("found in list \n");
			  return((void *)current);
			}
	        
		}
		idx++;
	       
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
//   printf("called place \n");
	size_t csize = GET_SIZE(HDRP(bp)); 

	if ((csize - asize) >= (2 * DSIZE)) { 
	  //struct free_block *first;
	  	// printf("splitting with size %i\n", (int) csize);
	    remove_free(bp);
		// printf("Inserted block = %p", bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		// printf("Remainder block = %p", bp);

		insert_free((csize - asize), bp);
		
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
	} else {
	    remove_free(bp);
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