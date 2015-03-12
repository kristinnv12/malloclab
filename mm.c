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

team_t team =
{
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

#define REQSIZE     8       /* doubleword size (bytes) */
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

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define NEXT_PTR(bp)       ((char *)(bp))
#define PREV_PTR(bp)       ((char *)(bp) + WSIZE)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - REQSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - REQSIZE)))

/* Print debugging information */
extern int verbose;
#define VERBOSED 0

#if VERBOSE == 1
# define PRINT_FUNC printf("Starting function: %s\n",__FUNCTION__);
#else
# define PRINT_FUNC
#endif

static char *heap_start;  /* pointer to the start of out heap. Note this is only global for debuging purposes*/
static char *free_startp; /* This points to the beginning of the free list */

static void *scan_for_free(size_t adjsize);
static void *new_free_block(size_t words);
static void place(void *alloc_ptr, size_t size_needed);
static void *coalesce(void *middle);
/*
static void mm_checkheap();
static void printblock(void *bp);
static void checkblock(void *bp);
*/
static void mm_insert(void *block);
static void mm_delete(void *block);

/*
 * mm_init - should find the start of the heap and reserve some initial space.
 */
int mm_init(void)
{
    PRINT_FUNC;

    heap_start = mem_sbrk(4 * WSIZE); //increment the break pointer by two double words

    if (heap_start == NULL)
    {
        return -1; //No more space for heap;
    }
                                                                            //                      -----------
    PUT(heap_start, 0);                                                     // padding              | padding |
                                                                            //                      |---------|
    PUT(heap_start + WSIZE, PACK(OVERHEAD, 1));                             // prolog header        |   PH    |
                                                                            //                      |---------|
    PUT(heap_start + REQSIZE, PACK(OVERHEAD, 1));                           // prolog footer        |   PF    |
                                                                            //                      |---------|
    PUT(heap_start + REQSIZE + WSIZE, PACK(0, 1));                          // epilog header        |   EH    |
                                                                            //                      -----------
    heap_start += REQSIZE;

    free_startp = NULL;
    //initilize some starting free space
    free_startp = new_free_block(CHUNKSIZE / WSIZE);

    //no more space available
    if (free_startp == NULL)   
    {
        return -1;
    }

    if (VERBOSED)
    {
        printf("\n");
        printf("Free list start pointer: %p\n", free_startp);
    }

    return 0;
}

/*
 * new_free_block - gets amount of words as input, increments brk pointer by needed bytes for requested word(s).
 *                  constructs the new free block with size tags, next and prev pointers and adjusts the epilog
 *                  footer.
 */
static void *new_free_block(size_t words)
{
    PRINT_FUNC;

    char *new_block;   //pointer to the new free/clean block
    size_t bytes;     //the number of bytes needed for the amount of words

    if (words < 2)
    {
        return NULL; //not enough space for next and prev pointers
    }

    if (words % 2)    //need to keep alignment as an even number
    {
        bytes = (words + 1) * WSIZE;
    }
    else
    {
        bytes = words * WSIZE;
    }

    new_block = mem_sbrk(bytes);  //increment the brk pointer to get more space

    if (new_block == (void *) - 1)
    {
        return NULL;    //something went terribly wrong
    }

    PUT(HDRP(new_block), PACK(bytes, 0));   //adding header size boundary tag
    PUT(FTRP(new_block), PACK(bytes, 0));   //adding footer sixe boundary tag

    //adjusting the epilog header
    PUT(HDRP(NEXT_BLKP(new_block)), PACK(0, 1));     

    //insert new free block to our list
    mm_insert(new_block);

    //mm_checkheap(verbose);

    return coalesce(new_block);

}
/*
 * mm_malloc - find a free block that fits our size so that it is a modulo 0 + overhead of 8 bytes
 *             if no space is found we increment mem_sbrk pointer for our new memory
 */
void *mm_malloc(size_t size)
{
    PRINT_FUNC;

    size_t adjsize;
    char *allocspacePtr;
    size_t extend_size;

    /* Base case: 0 */
    if (size <= 0)
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
        adjsize = REQSIZE * ((size + (OVERHEAD) + (REQSIZE - 1)) / REQSIZE);
    }

    //scan for free space
    allocspacePtr = scan_for_free(adjsize);

    if (VERBOSED)
    {
        printf("Allocspacept gave: %p\n", allocspacePtr);
    }

    if (allocspacePtr != NULL)
    {
        //found free space that fits the adjusted size
        place(allocspacePtr, adjsize);
        return allocspacePtr;
    }

    extend_size = MAX(adjsize, CHUNKSIZE);
    
    //we just allocate more space
    allocspacePtr = new_free_block(extend_size / WSIZE);

    if (allocspacePtr == NULL)
    {
        return NULL;
    }

    //place block in heap
    place(allocspacePtr, adjsize);

    //mm_checkheap(verbose);

    return allocspacePtr;
}

/*
 * place - place block of size adjSize at the start of pointer allocPtr
 */
static void place(void *alloc_ptr, size_t size_needed)
{
    PRINT_FUNC;

    //fetch the size of the block given to us
    size_t block_size = GET_SIZE(HDRP(alloc_ptr));      

    size_t block_remainder = block_size - size_needed;

    //check if reallocating
    if(!GET_ALLOC(HDRP(alloc_ptr)))
    {
        //delete block from our free list
        mm_delete(alloc_ptr);
    }

    if (block_remainder >= (REQSIZE + OVERHEAD))
    {
        //split block in two
        PUT(HDRP(alloc_ptr), PACK(size_needed, 1));
        PUT(FTRP(alloc_ptr), PACK(size_needed, 1));

        //We have space for a new free block
        alloc_ptr = NEXT_BLKP(alloc_ptr);
        PUT(HDRP(alloc_ptr), PACK(block_remainder, 0));
        PUT(FTRP(alloc_ptr), PACK(block_remainder, 0));
        
        //insert new block to the start of our free list
        mm_insert(alloc_ptr);
        
    }
    else
    {
        //use the whole block
        PUT(HDRP(alloc_ptr), PACK(block_size, 1));
        PUT(FTRP(alloc_ptr), PACK(block_size, 1));
    }
}
/*
 * mm_delete - deleting a free block from our free list
 */
void mm_delete(void *block)
{

    PRINT_FUNC;
    char *next;
    char *prev;

    next = (char *)GET(NEXT_PTR(block));
    prev = (char *)GET(PREV_PTR(block));

    if (next == NULL && prev != NULL)           //Case 0: At the end of a list
    {
        GET(NEXT_PTR(prev)) = (size_t)next;
    }
    else if (prev == NULL && next != NULL)      //Case 1: At the start of the list
    {
        GET(PREV_PTR(next)) = (size_t)prev;
        free_startp = next;
    }
    else if (prev == NULL && next == NULL)      //Case 2: Only block left in list
    {
        free_startp = NULL;
    }
    else if (prev != NULL && next != NULL)      //Case 3: Somewhere in the middle of the list
    {
        GET(NEXT_PTR(prev)) = (size_t)next;
        GET(PREV_PTR(next)) = (size_t)prev;
    }
}
/*
 * mm_insert - inserting new free block to our free list.
 */
void mm_insert(void *block)
{

    PRINT_FUNC;
    GET(PREV_PTR(block)) = 0;

    if (free_startp == NULL)                //case 0: Inserting in an empty list
    {
        GET(NEXT_PTR(block)) = 0;
        free_startp = block;
    }
    else                                    //case 1: Inserting in a non empty list
    {
        GET(PREV_PTR(free_startp)) = (size_t)block;
        GET(NEXT_PTR(block)) = (size_t)free_startp;
        free_startp = block;
    }

}
/*
 * mm_free - Freeing a block but does not coalesce the freed space.
 */
void mm_free(void *block)
{
    PRINT_FUNC;

    size_t ptrSize = GET_SIZE(HDRP(block));

    //Free the header and footer of given pointer
    PUT(HDRP(block), PACK(ptrSize, 0));
    PUT(FTRP(block), PACK(ptrSize, 0));

    //insert block at the start of our free list
    mm_insert(block);

    //mm_checkheap(verbose);

    coalesce(block);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{

    /*
     * #1: See if next block is free, then simply expand.
     * #2: See if new size is less then the current block size, then we cut the block in half.
     * #3: Need to copy contents to another location
     */

    PRINT_FUNC;

    void *newptr;
    size_t copySize;

    copySize = GET_SIZE(HDRP(ptr));

    // We don't have to realloc if new size == copySize
    if (copySize == size)
    {
        return ptr;
    }

    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }   

    if (size <= REQSIZE)
    {
        size = REQSIZE + OVERHEAD;
    }
    else
    {
        size = REQSIZE * ((size + (OVERHEAD) + (REQSIZE - 1)) / REQSIZE);
    }

    if (size < copySize)
    {
        place(ptr, size);
        return ptr;
    }

    size_t right = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t new_size = (GET_SIZE(HDRP(NEXT_BLKP(ptr)))) + copySize;
    size_t right_remainder = new_size - size;

    // 1. Next block is free, 2. Size of both blocks is big enough, 3. Not the Epilog header
    if(right == 0 && new_size > size && GET_SIZE(HDRP(NEXT_BLKP(ptr))) != 0)
    {
        //remainder of the block is big enough to be a free block
        if(right_remainder >= REQSIZE + OVERHEAD)
        {
            mm_delete(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));

            ptr = NEXT_BLKP(ptr);
            PUT(HDRP(ptr), PACK(right_remainder, 0));
            PUT(FTRP(ptr), PACK(right_remainder, 0));
            mm_insert(ptr); 
            return PREV_BLKP(ptr);
        }
        else
        {
            //otherwise we use the whole block
            mm_delete(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
        }

        return ptr;
    }

    //find new block
    newptr = mm_malloc(size);

    if (newptr == NULL)
    {
        printf("ERROR: mm_realloc\n");
        exit(1);
    }


    //copy content to new adress
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}

/*
 * coalecse -check the two neighboring blocks for alocation, if possible we will merge these blocks together
 */
static void *coalesce(void *middle)
{
    PRINT_FUNC;
    size_t left = GET_ALLOC(FTRP(PREV_BLKP(middle)));
    size_t right = GET_ALLOC(HDRP(NEXT_BLKP(middle)));
    size_t size = GET_SIZE(HDRP(middle));


    if(left && right)                                   //Case 0: No free block
    {
        return middle;
    }
    
    //remove the node from our list
    mm_delete(middle);
    
    if (left && !right)                                 //Case 1: Right neigbor is a free block
    {
        mm_delete(NEXT_BLKP(middle));
        size += GET_SIZE(HDRP(NEXT_BLKP(middle)));
        PUT(HDRP(middle), PACK(size, 0));
        PUT(FTRP(middle), PACK(size, 0));
    }
    else if (!left && right)                            //Case 2: Left neigbor is a free block
    {
        mm_delete(PREV_BLKP(middle));
        size += GET_SIZE(HDRP(PREV_BLKP(middle)));
        PUT(HDRP(PREV_BLKP(middle)), PACK(size, 0));
        PUT(FTRP(middle), PACK(size, 0));
        middle = PREV_BLKP(middle);
    }
    else if (!left && !right)                           //Case 4: Both neigbors are free blocks
    {
        mm_delete(PREV_BLKP(middle));
        mm_delete(NEXT_BLKP(middle));
        size += GET_SIZE(HDRP(PREV_BLKP(middle))) + GET_SIZE(FTRP(NEXT_BLKP(middle)));
        PUT(HDRP(PREV_BLKP(middle)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(middle)), PACK(size, 0));
        middle = PREV_BLKP(middle);
    }

    //insert the edited node in again
    mm_insert(middle);

    return middle;
}
/*
 * scan_for_free - Scans the our explisit list for a block that suits the requierd size.
 */
static void *scan_for_free(size_t reqsize)
{
    PRINT_FUNC;
    char *curr;

    //Start on the head of the heap and run down it
    for (curr = free_startp; curr != NULL; curr = (char *)GET(NEXT_PTR(curr)))
    {
        //Found space fits the requierd size
        if (reqsize <= GET_SIZE(HDRP(curr)))
        {
            return curr;
        }
    }
    return NULL; // need more space
}

/*
 * mm_checkheap - Our life saving heap checker, can print out the whole heap, print the free list, check Epilog and prolog headers 
 * for coruption, see if free list next pointers are out of bounds, check for header and footer consistency and check for block
 * alignment
 */
 /*
void mm_checkheap(int verbose)
{
    PRINT_FUNC;

    char *bp = heap_start;

    if (verbose)
    {
        if(verbose == 2)
        {
            printf("Heap (%p):\n", heap_start);
        }

        if ((GET_SIZE(HDRP(heap_start)) != REQSIZE) || !GET_ALLOC(HDRP(heap_start)))
        {
            printf("Bad prologue header\n");
        }
        checkblock(heap_start);
    }

    if (verbose == 2)
    {
        for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = (char *)NEXT_BLKP(bp))
        {
            printblock(bp);
            checkblock(bp);
        }

        printblock(bp);
        char *curr;

        for (curr = free_startp; curr != NULL; curr = (char *)GET(NEXT_PTR(curr)))
        {

            if (curr < (char *)mem_heap_lo() || curr > (char *)mem_heap_hi())
            {
                printf("free list adress (%p) out of bounds \n", curr);
                break;
            }
            else
            {
                printf("(%p)->", curr);
            }
        }
        printf("\n");

        if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        {
            printf("Bad epilogue header\n");
        }
    }

}
*/

/*
 * printblock - helperfunction for checkheap()
 */
 /*
static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    char *next_block, *prev_block;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
    next_block = (char *)GET(NEXT_PTR(bp));
    prev_block = (char *)GET(PREV_PTR(bp));

    if (hsize == 0)
    {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c] prev-block: [%p] next-block: [%p]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'),
           prev_block, next_block);
}
*/
/*
 * checkblock - helperfunction for checkheap()
 */
 /*
static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
    {
        printf("Error: %p is not doubleword aligned\n", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
    {
        printf("Error: header does not match footer\n");
    }
}
*/