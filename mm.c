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
#define DSIZE     8
//TODO change over head to include next and prev pointers
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
#define VERBOSED 1

#if VERBOSED == 1
# define PRINT_FUNC printf("Starting function: %s\n",__FUNCTION__);
#else
# define PRINT_FUNC
#endif

static char *heap_start;  /* pointer to the start of out heap*/
static char *free_startp; /* This points to the beginning of the free list */
static char *free_endp = 0; /* This pointes to the end of the free list */

static void *scan_for_free(size_t adjsize);
static void *new_free_block(size_t words);
static void place(void *alloc_ptr, size_t size_needed);
static void *coalesce(void *middle);
static void mm_checkheap();

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
    //                              -----------
    PUT(heap_start, 0);                                                     //padding               | padding |
    //                           |---------|
    PUT(heap_start + WSIZE, PACK(OVERHEAD, 1));      //prolog header    |   PH    |
    //                           |---------|
    PUT(heap_start + REQSIZE, PACK(OVERHEAD, 1));   //prolog footer      |   PF    |
    //                            |---------|
    PUT(heap_start + REQSIZE + WSIZE, PACK(0, 1));    //epilog header     |   EH    |
    //                           -----------
    heap_start += REQSIZE;

    if (free_startp = new_free_block(CHUNKSIZE / WSIZE) == NULL )   //initilize some starting free space
    {
        return -1;
    }

    free_endp = free_startp;    /* Let end of free list point to the beginning of the list*/

    if (VERBOSED)
    {
        printf("\n");
        printf("Free list start pointer: %p\n", free_startp);
        printf("Free list end pointer: %p\n", free_endp);
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
    PRINT_FUNC;

    char *mr_clean;   //pointer to the new free/clean block
    size_t bytes;     //the number of bytes needed for the amount of words

    if (words % 2)    //need to keep alignment as an even number
    {
        bytes = (words + 1) * WSIZE;
    }
    else
    {
        bytes = words * WSIZE;
    }

    mr_clean = mem_sbrk(bytes);  //increment the brk pointer to get more space

    if (mr_clean == (void *) - 1)
    {
        return NULL;    //something went terribly wrong
    }

    PUT(HDRP(mr_clean), PACK(bytes, 0));   //adding header size boundary tag
    PUT(FTRP(mr_clean), PACK(bytes, 0));   //adding footer sixe boundary tag
    PUT(NEXT_PTR(mr_clean), 0xdeadbeef);
    PUT(PREV_PTR(mr_clean), 0x1337b00b);

    mm_checkheap(1);

    //TODO: add the next and prev pointers to the block

    //TODO: Can we assume that the epilog header is the next block when we are working with an explicit list ?!?!?!
    PUT(HDRP(NEXT_BLKP(mr_clean)), PACK(0, 1));     //changing the epilog header

    //TODO: Check if the previous block is free and coalesce
    return coalesce(mr_clean);

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
    allocspacePtr = scan_for_free(adjsize); /* Same as find_fit in debugging.mp4 */

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

    place(allocspacePtr, adjsize);
    mm_checkheap();
    return allocspacePtr;
}

/*
 * place - place block of size adjSize at the start of pointer allocPtr
 */
static void place(void *alloc_ptr, size_t size_needed)
{
    PRINT_FUNC;

    size_t block_size = GET_SIZE(HDRP(alloc_ptr));      //fetch the size of the block given to us

    size_t block_remainder = block_size - size_needed;

    if (block_remainder >= (REQSIZE + OVERHEAD))
    {
        PUT(HDRP(alloc_ptr), PACK(size_needed, 1));
        PUT(FTRP(alloc_ptr), PACK(size_needed, 1));
        alloc_ptr = NEXT_BLKP(alloc_ptr);
        PUT(HDRP(alloc_ptr), PACK(block_remainder, 0));     //We have space for a new free block, split the block up
        PUT(FTRP(alloc_ptr), PACK(block_remainder, 0));
        PUT(NEXT_PTR(alloc_ptr), 0xdeadbeef);
        PUT(PREV_PTR(alloc_ptr), 0x1337b00b);
        //TODO: Add next and prev pointers
        mm_checkheap(1);
    }
    else
    {
        PUT(HDRP(alloc_ptr), PACK(block_size, 1));
        PUT(FTRP(alloc_ptr), PACK(block_size, 1));
    }
}

/*
 * mm_free - Freeing a block but does not coalesce the freed space.
 */
void mm_free(void *williamWallace)
{
    PRINT_FUNC;

    /* Base case: NULL */
    if (!williamWallace)
    {
        return;
    }

    size_t ptrSize = GET_SIZE(HDRP(williamWallace));

    //Free the header and footer of given pointer
    PUT(HDRP(williamWallace), PACK(ptrSize, 0));
    PUT(FTRP(williamWallace), PACK(ptrSize, 0));
    PUT(NEXT_PTR(williamWallace), 0xdeadbeef);
    PUT(PREV_PTR(williamWallace), 0x1337b00b);

    mm_checkheap(1);
    //FREEDOM!!!
    coalesce(williamWallace);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    PRINT_FUNC;

    //TODO: Check if it is possible to extend the current memory adress rather than just reserving more space
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);

    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    if (newptr == NULL)
    {
        printf("ERROR: mm_realloc\n");
        exit(1);
    }

    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
    {
        copySize = size;
    }
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

    /* Cases mentioned on page 825 */

    size_t left = GET_ALLOC(FTRP(PREV_BLKP(middle)));
    size_t right = GET_ALLOC(HDRP(NEXT_BLKP(middle)));
    size_t size = GET_SIZE(HDRP(middle));

    /* Case 1: The previous and next blocks are both allocated. */
    if (left && right)      //no free block to merge
    {
        return middle;
    }

    /* Case 2: The previous block is allocated and the next block is free. */
    else if (left && !right)    //right neigbor is a free block
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(middle)));
        PUT(HDRP(middle), PACK(size, 0));
        PUT(FTRP(middle), PACK(size, 0));
    }

    /* Case 3: The previous block is free and the next block is allocated. */
    else if (!left && right)    //left neigbor is a free block
    {
        size += GET_SIZE(HDRP(PREV_BLKP(middle)));
        PUT(HDRP(PREV_BLKP(middle)), PACK(size, 0));
        PUT(FTRP(middle), PACK(size, 0));
        middle = PREV_BLKP(middle);
    }

    /* Case 4: The previous and next blocks are both free. */
    else if (!left && !right)    //both neigbors are free blocks
    {
        size += GET_SIZE(HDRP(PREV_BLKP(middle))) + GET_SIZE(FTRP(NEXT_BLKP(middle)));
        PUT(HDRP(PREV_BLKP(middle)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(middle)), PACK(size, 0));
        middle = PREV_BLKP(middle);
    }


    /* Now we add the freed pointer to the free list */

    return middle;
}
/*
* scan_for_free - Scans the heap for the requierd size.
*/
static void *scan_for_free(size_t reqsize)
{
    PRINT_FUNC;

    void *free_list_bp;

    for (free_list_bp = free_startp; !GET_ALLOC(HDRP(free_list_bp)) ; free_list_bp = NEXT_BLKP(free_list_bp))
    {
        if (reqsize <= GET_SIZE(HDRP(free_list_bp)) )
        {
            return free_list_bp;
        }
    }

    return NULL;

    /* Kiddakode
    void *curr;

    //Start on the head of the heap and run down it
    for (curr = heap_start; GET_SIZE(HDRP(curr)) > 0; curr = NEXT_BLKP(curr))
    {
        //Found space fits the requierd size
        if (!GET_ALLOC(HDRP(curr)) && (reqsize <= GET_SIZE(HDRP(curr))))
        {
            return curr;
        }
    }
    return NULL; // need more space*/
}

//TODO: Heap consistency cheker

void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
    printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose) 
        printblock(bp);
    checkblock(bp);
    }
     
    if (verbose)
    printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    printf("Bad epilogue header\n");
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
       hsize, (halloc ? 'a' : 'f'), 
       fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
    printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}