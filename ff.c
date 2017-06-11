/*
 * mm.c
 *
 * This is the only file you should modify.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
/* NB: this code calls a 32-bit quantity a word */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_FREE(bp)  (*(char **)(bp + DSIZE))
#define PREV_FREE(bp)  (*(char **)(bp))
/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* pointer to first block */  
static char *free_listp = 0;
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)
static void *extend_heap(size_t words);
static void insertF(void *bp);
static void removeF(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void checkBlock(void *bp);
static void printBlock(void *bp);
static void *coalesce(void *bp);
/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
 if ((heap_listp = mem_sbrk(4*DSIZE)) == NULL)
    return -1;
  PUT(heap_listp, 0);                        /* alignment padding */
  PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
  PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
  PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
  heap_listp += DSIZE;
	free_listp = heap_listp;
	
  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
  return 0;
}
static void place(void *bp, size_t asize)
{
 size_t csize = GET_SIZE(HDRP(bp));   

  if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    removeF(bp);
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
  }
  else { 
 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
	removeF(bp);
	}
}

/*
 * malloc
 */
void *mm_malloc (size_t size) {
     size_t asize = MAX(ALIGN(size) + DSIZE, DSIZE*4);
     //allocate to either an aligned size or the smallest possible block size, which is 4 words(the header, the prev block, the next block, the footer)
     size_t extend;
     if(size <= 0)
			return NULL;
     void *bp = find_fit(asize);
     if(bp != NULL)
     {
			place(bp, asize);
			return bp;
     
     }
     extend = MAX(asize, CHUNKSIZE);
     bp = extend_heap(extend/WSIZE);
     if(bp == NULL)
			return NULL;
		 place(bp, asize);
		 return bp;
}
static void *find_fit(size_t asize)
{
	void *bp = free_listp;
	for(; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE(bp))
		if(GET_SIZE(HDRP(bp)) >= asize)
			return bp;
	return NULL;

}

/*
 * free
 */
void mm_free (void *ptr) {
    if(ptr == NULL)
			return;
		size_t size = GET_SIZE(HDRP(ptr));
		
		
		PUT(FTRP(ptr), PACK(size, 0));
		//for some reason getting rid of this header pack caused a lot of tests to pass
		//but that's because I was wrong before and now I need it again lol
		PUT(HDRP(ptr), PACK(size, 0));
		coalesce(ptr);
		
}


/*
 * realloc - you may want to look at mm-naive.c
 */
void *mm_realloc(void *oldptr, size_t size) {
   size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    mm_free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return mm_malloc(size);
  }

  newptr = mm_malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize = *SIZE_PTR(oldptr);
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  mm_free(oldptr);

  return newptr;
}


/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *mm_calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = mm_malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}
static void insertF(void *ptr)
{
	NEXT_FREE(ptr) = free_listp;
	PREV_FREE(free_listp) = ptr;
	PREV_FREE(ptr) = NULL;
	free_listp = ptr;
}

/*
 * removeF - Removes a block from the free list
 * This function takes a block pointer of the block to remove as a
 * parameter.
 */
static void removeF(void *ptr)
{
	if(PREV_FREE(ptr))
		NEXT_FREE(PREV_FREE(ptr)) = NEXT_FREE(ptr);
	else
		free_listp = NEXT_FREE(ptr);
		
	PREV_FREE(NEXT_FREE(ptr)) = PREV_FREE(ptr);

}
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if(size < DSIZE*4)
		size = DSIZE*4;
	if((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
	void *ret = coalesce(bp);
	return ret;
}
static void *coalesce(void *bp)
{
	size_t pAlloc;
	pAlloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
	size_t nAlloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	if(!pAlloc && nAlloc)
	{
		size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
		bp = PREV_BLKP(bp);
		removeF(bp);
		PUT(HDRP(bp), PACK(size, 0));//turn this into a function or macro ffs
		PUT(FTRP(bp), PACK(size, 0));//turn this into a function or macro ffs
	}
	else if(pAlloc && !nAlloc)
	{
		size+= GET_SIZE(HDRP(NEXT_BLKP(bp)));
		removeF(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));//turn this into a function or macro ffs
		PUT(FTRP(bp), PACK(size, 0));//turn this into a function or macro ffs
	}
	else if(!pAlloc && !nAlloc)
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
		removeF(PREV_BLKP(bp));
		removeF(NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	insertF(bp);
	return bp;
}
/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p < mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
}
