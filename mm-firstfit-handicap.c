/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * Note: This assignment is a _baseline_ for the performance grade.
 * You will need to exceed the performance of this implicit first-fit placement
 * (which is about 54/100).
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/* Team structure */
team_t team = {
    "implicit first fit", 
    "Dave OHallaron", "droh",
    "", "",
    "", ""
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define REQSIZE     8
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/*(which is about 54/100).* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{

    heap_listp = mem_sbrk(4*WSIZE); //increment the break pointer by two double words

    if(heap_listp == NULL)
    {
        return -1; //No more space for heap;
    }
                                                        //                                  -----------
    PUT(heap_listp, 0);                                 //padding                           | padding |
                                                        //                                  |---------|
    PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1));         //prolog header                     |   PH    |
                                                        //                                  |---------|
    PUT(heap_listp + REQSIZE, PACK(OVERHEAD, 1));       //prolog footer                     |   PF    |
                                                        //                                  |---------|
    PUT(heap_listp + REQSIZE + WSIZE, PACK(0, 1));      //epilog header                     |   EH    |
                                                        //                                  -----------
    heap_listp += REQSIZE;

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL )    //initilize some starting free space
    {
        return -1;
    }

    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    size_t adjsize;
    char *allocspacePtr;
    size_t extend_size;

    //base case: 0
    if(size <= 0)
    {
        return NULL;
    }

    //Must make our size a modulo 0 + overhead of 8 bytes
    if (size <= REQSIZE)
    {
        adjsize = REQSIZE + OVERHEAD;
    }
    else
    {
        adjsize = REQSIZE * ((size + (OVERHEAD) + (REQSIZE-1)) / REQSIZE);
    }
    
    //scan for free space
    allocspacePtr = find_fit(adjsize);

    if(allocspacePtr != NULL){

        //found free space that fits the adjusted size
        place(allocspacePtr, adjsize);
        return allocspacePtr;
    }

    extend_size = MAX(adjsize, CHUNKSIZE);
    //we just allocate more space

    allocspacePtr = extend_size(extend_size/WSIZE);

    if(allocspacePtr == NULL)
    {
        return NULL;
    }

    place(allocspacePtr, adjsize);
    return allocspacePtr;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
    return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
    copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    /*
    char *bp;
    size_t size;
	
    //Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
	return NULL;

    //Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));         /* free block header
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header

    //Coalesce if the previous block was free
    return bp;*/

    char *mr_clean;   //pointer to the new free/clean block
    size_t bytes;     //the number of bytes needed for the amount of words

    if(words & 2)     //need to keep alignment as an even number
    {
        bytes = (words + 1) * WSIZE;
    }
    else
    {
    bytes = words * WSIZE;
    }

    mr_clean = mem_sbrk(bytes);  //increment the brk pointer to get more space

    if(mr_clean == (void *)-1)
    {
        return NULL;    //something went terribly wrong
    }

    PUT(HDRP(mr_clean), PACK(bytes, 0));   //adding header size boundary tag
    PUT(FTRP(mr_clean), PACK(bytes, 0));   //adding footer sixe boundary tag

    //TODO: add the next and prev pointers to the block

    //TODO: Can we assume that the epilog header is the next block when we are working with an explicit list ?!?!?!
    PUT(HDRP(NEXT_BLKP(mr_clean)), PACK(0, 1));     //changing the epilog header

    //TODO: Check if the previous block is free and coalesce
    return mr_clean;
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
	    return bp;
	}
    }
    return NULL; /* no fit */
}
