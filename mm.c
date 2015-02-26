/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * === User information ===
 * Group: PlainStupid 
 * User 1: kristinnv12
 * SSN: 0208923829
 * User 2: ragnarp12 
 * SSN: 2801872169 
 * === End User Information ===
 ********************************************************/
team_t team = {
    /* Group name */
    "PlainStupid",
    /* First member's full name */
    "Kristinn Vignisson",
    /* First member's email address */
    "kristinnv12@ru.is",
    /* Second member's full name (leave blank if none) */
    "Ragnar Pálsson",
    /* Second member's email address (leave blank if none) */
    "ragnarp12@ru.is",
    /* Leave blank */
    "",
    /* Leave blank */
    ""
};

/* Basic constants and macros (from mm-firstfit.c)*/
#define REQSIZE       8       /* doubleword size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define WSIZE       4       /* word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/*Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - REQSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - REQSIZE)))

static char *heap_start;  /* pointer to first block */  

static void *scan_for_free(size_t adjsize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    //TODO: Find the Start of the heap and store it globaly.
    heap_start = 0;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t adjsize;
    char *alocspacePtr;

    //base case: 0
    if(size <=0)
    {
        return NULL;
    }

    //Must make our size a modulo 0 + overhead of 8 bytes
    if (size <= REQSIZE)
    adjsize = REQSIZE + OVERHEAD;
    else
    adjsize = REQSIZE * ((size + (OVERHEAD) + (REQSIZE-1)) / REQSIZE);
    
    //scan for free space
    alocspacePtr = scan_for_free(adjsize);

    if(alocspacePtr != NULL){

        //found free space that fits the adjusted size
        //TODO: understand place function and impliment
        return alocspacePtr;
    }
    else
    {
        //we just allocate more space
        //TODO: Find a more optimal way of finding how much space we need to reserve
        int newsize = ALIGN(size + SIZE_T_SIZE);
        void *p = mem_sbrk(newsize);
        if (p == (void *)-1)
    	return NULL;
        else {
            *(size_t *)p = size;
            return (void *)((char *)p + SIZE_T_SIZE);
        }
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *williamWallace)
{
    size_t ptrSize = GET_SIZE(HDRP(williamWallace));

    //Free the header and footer of given pointer
    PUT(HDRP(williamWallace), PACK(ptrSize, 0));
    PUT(FTRP(williamWallace), PACK(ptrSize, 0));
    //FREEDOM!!!

    //TODO: need to check if the freed space can be joined with the next or previous block
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    //TODO: Check if it is possible to extend the current memory adress rather than just reserving more space
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

/*
* scan_for_free - Scans the heap for the requierd size.
*/
static void *scan_for_free(size_t reqsize)
{
    void *curr;

    //Start on the head of the heap and run down it
    for (curr = heap_start; GET_SIZE(HDRP(curr)) > 0; curr = NEXT_BLKP(curr)) {
        //Found space fits the requierd size
        if (!GET_ALLOC(HDRP(curr)) && (reqsize <= GET_SIZE(HDRP(curr)))) {
            return curr;
        }
    }
    return NULL; /* need more space */
}