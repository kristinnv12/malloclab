/*
 * mm.c - Explicit free list solution using LIFO free policy, optimal fit placement (perfect fit search) and boundary tag coalescing.
 * 
 * Our solution will be a explicit free list. We will free blocks using the LIFO policy for simplicity, that is a newly freed block will be
 * added at the begining/root of our free list. For our list we will need 2 extra word per each block for our links, that is the forward
 * and back pointer since our next free block could be anywhere in the physical memory, that is the list does not lie linear in memory
 * and therefore it is not sufficient to just store the size of each block as you can do in the implicit list. We will also still
 * need our boundary tags like in the implicit list solution for the coalescing method. We dont want to call coalesce everytime
 * we free a block (imideate coalesce) but rather use deffered coalescing, we plan on calling coalesce only as we are scaning
 * our list for free space. When scanning the list for free blocks we will first try to find a perfect fit for our block,
 * if the perfect fit does not exist we will try again but lower our expectations and make do with a little bit of
 * wasted space, we will try to find the perfect balance in time usage and the amount of fragmentation we are
 * willing to put up with until we get desprate and expand our heap space by incrementing our brk pointer.
 * We are going to store a pointer to the start of our heap in a global varialble and this variable will 
 * be reset at initilazation. 
 *
 *  This is how each free block should be structured:
 *
 *      |--------------------------------------------------------------------------------|
 *      | Size boundary tag| Nexr ptr | Prev ptr | Payload & padding | Size bounadry tag |
 *      |--------------------------------------------------------------------------------|
 *  
 *  And this is how the list it self should be structured (pretty much the same idea as in the implicit list solution):
 *
 *      |-------------------------------------------------------------------------|
 *      | Prolog block (header & footer) | The free blocks | Epilog block (header)| 
 *      |-------------------------------------------------------------------------|
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
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

static char *heap_start;  /* pointer to the start of out heap*/  

static void *scan_for_free(size_t adjsize);

/* 
 * mm_init - should find the start of the heap and reserve some initial space.
 */
int mm_init(void)
{
    heap_start = mem_sbrk(2*REQSIZE); //increment the break pointer by two double words

    if(heap_start == NULL)
    {
        return -1; //No more space for heap;
    }
                                                                                            -----------
    PUT(heap_start, 0);                                 //padding                           | padding |
                                                                                            |---------|
    PUT(heap_start + WSIZE, PACK(OVERHEAD, 1));         //prolog header                     |   PH    |
                                                                                            |---------|
    PUT(heap_start + REQSIZE, PACK(OVERHEAD, 1));       //prolog footer                     |   PF    |
                                                                                            |---------|
    PUT(heap_start + REQSIZE + WSIZE, PACK(0, 1));      //epilog header                     |   EH    |
                                                                                            -----------

    if(new_free_block(CHUNKSIZE/WSIZE) == NULL )    //initilize some starting free space
    {
        return -1;
    }

    return 0;
}

/*
 * new_free_block - gets amount of words as input, increments brk pointer by needed bytes for requested word(s).
 *                  constructs the new free block with size tags, next and prev pointers and adjusts the epilog
                    footer.
 */
static void *new_free_block(size_t words)
{
    char *mr_clean;   //pointer to the new free/clean block
    size_t bytes;       //the number of bytes needed for the amount of words

    if(words & 2 == 0)          //need to keep alignment as an even number
    {
        bytes = words * WSIZE;  
    }
    else
    {
        bytes = (words + 1) * WSIZE;
    }

    mr_clean = mem_sbrk(bytes)  //increment the brk pointer to get more space

    if(mr_clean == (void *)-1)
    {
        return NULL;    //something went terribly wrong
    }

    PUT(HDRP(mr_clean), PACK(size, 0));   //adding header size boundary tag
    PUT(FTRP(mr_clean), PACK(size, 0));   //adding footer sixe boundary tag

    //TODO: add the next and prev pointers to the block

    //TODO: Can we assume that the epilog header is the next block when we are working with an explicit list ?!?!?!
    PUT(HDRP(NEXT_BLKP(mr_clean)), PACK(0, 1));     //changing the epilog header

    //TODO: Check if the previous block is free and coalesce
    return mr_clean;

}
/* 
 * mm_malloc - find a free block that fits our size so that it is a modulo 0 + overhead of 8 bytes
 *             if no space is found we increment mem_sbrk pointer for our new memory
 */
void *mm_malloc(size_t size)
{

    size_t adjsize;
    char *allocspacePtr;

    //base case: 0
    if(size <= 0)
    {
        return NULL;
    }

    //Must make our size a modulo 0 + overhead of 8 bytes
    if (size <= REQSIZE)
    adjsize = REQSIZE + OVERHEAD;
    else
    adjsize = REQSIZE * ((size + (OVERHEAD) + (REQSIZE-1)) / REQSIZE);
    
    //scan for free space
    allocspacePtr = scan_for_free(adjsize);

    if(allocspacePtr != NULL){

        //found free space that fits the adjusted size
        place(allocspacePtr)
        return allocspacePtr;
    }

    extend_size = MAX(adjsize, CHUNKSIZE);
    //we just allocate more space

    allocspacePtr = new_free_block(extend_size/WSIZE);

    if(alloc_ptr == NULL)
    {
        return NULL;
    }

    place(allocspacePtr, adjsize);
    return allocspacePtr;
}

/*
 * place - place block of size adjSize at the start of pointer allocPtr
 */
static void place(void *alloc_ptr, size_t size_needed)
{
    size_t block_size = GET_SIZE(HDRP(alloc_ptr));      //fetch the size of the block given to us

    size_t block_remainder = block_size - size_needed;

    PUT(HDRP(alloc_ptr), PACK(adjsize, 1));
    PUT(FTRP(alloc_ptr), PACK(adjsize, 1));

    if(block_remainder >= (REQSIZE + OVERHEAD))
    {
        alloc_ptr = NEXT_BLKP(alloc_ptr);
        PUT(HDRP(alloc_ptr), PACK(block_remainder, 0));     //We have space for a new free block, split the block up
        PUT(FTRP(alloc_ptr), PACK(block_remainder, 0));
        //TODO: Add next and prev pointers
    }
}

/*
 * mm_free - Freeing a block but does not coalesce the freed space.
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

//TODO: Heap consistency cheker