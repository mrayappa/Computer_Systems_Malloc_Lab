/*
 * mm-.c
 *
 * This dynamic memory allocator manages the memory by creating
 * an array of contiguous blocks (allocated & free) on the heap.
 * 
 * Now the free blocks are organized in several linked lists 
 * that only contain blocks less than particular sizes, essentially
 * implementing a segregated list.
 *
 * Both allocated and free blocks have headers that designate the 
 * size of the blocks, current block's allocation status, and 
 * previous block's allocation status.
 *
 * With free blocks, footers, identical to headers, are included at
 * the end of each block for possible coalescing.  Additionally, 
 * pointers to the previous and next free block in the segregated list
 * are also included in each free block's body.
 *
 * When there are malloc requests, the memory allocator searches through
 * the free lists to determine which one to start looking at first based 
 * on requested size and continuing onward with lists with bigger size
 * restrictions.  If a free block is found, that block is assigned, and
 * if not, memory will be extended beyond the current heap size.  
 * Splitting can occur if assigned free block is larger than requested 
 * size AND the remaining size is larger than the minimum free block size.
 * The respective header of the allocated block will be updated 
 * accordingly, while the footer and previous and next pointers are 
 * removed.
 *
 * When there are free requests, the memory allocator determines the size
 * of the freed block and adds (links) it to the appropriate linked list
 * by updating the header, adding the footer, and previous and next 
 * pointers to free blocks in the free list.  
 *
 * Any time when there's an addition of a free block, whether from 
 * free or heap extension, coalescing is performed to possibly create 
 * a block of a larger size to reduce fragmentation.  Now, the blocks to 
 * be coalesced will be first removed from the original lists they belong 
 * in before joining in to form a bigger block and adding it to a 
 * (possibly different) free list.
 *
 * Implementation with Segregated free list and LRU
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>

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


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */



/* constants */
/* double word (8) alignment */
#define ALIGNMENT 8

#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   176 /*384*/ 
#define OVERHEAD    8
#define MINBLOCK    24

/* for storing in lower 3 bits of header in allocated blocks
    and header & footer in free blocks */
#define PREVALLOC   2
#define CURRALLOC   1

/* offsets for segregated list pointers to list heads */
#define LIST1OS     0 
#define LIST2OS     8
#define LIST3OS     16
#define LIST4OS     32
#define LIST5OS     40

/* constants to help iterating through appropriate lists */
#define I1OS        0
#define I2OS        1
#define I3OS        2
#define I4OS        3 
#define I5OS        4

/* actual max size limit of each list */
#define LIST1S      29
#define LIST2S      1000
#define LIST3S      4000
#define LIST4S      8100

/* total number of segregated lists */
#define TOTALLIST   5 



/* function macros */
#define MAX(x, y)   ((x) > (y) ? (x) : (y))
#define MIN(x, y)   ((x) < (y) ? (x) : (y))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write 8 bytes at address p */
#define GET(p)      (*((size_t*) (p)))
#define PUT(p, val) (*((size_t*) (p)) = (val))

/* Read and write 4 bytes at address p */
#define GET4(p)     (*((uint32_t*) (p)))
#define PUT4(p, val)(*((uint32_t*) (p)) = (val))

  
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET4(p) & ~0x7)
#define GET_ALLOC(p)        (GET4(p) & 0x1)

/* Read whether previous block is allocated or if prologue */
#define GET_PREV_ALLOC(p)   (GET4(p) & 0x2)
#define GET_PREV_PROLO(p)   (GET4(p) & 0x4)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char*)(bp) - WSIZE)
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp)   ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE))
#define PREV_BLKP(bp)   ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))

/* Given free block addr bp, compute addresses in which the previous
    and next free blocks' addresses are stored */
#define FREE_NEXT_ADD(bp)   ((char*) ((char*)(bp)))      
#define FREE_PREV_ADD(bp)   ((char*) ((char*)(bp) + DSIZE))



/* helper functions */
static void add2list(char* bp, size_t size);
static void remflist(char* bp, size_t size);

static void* extend_heap(size_t words);
static void* coalesce(void* bp);

static void* find(size_t start_size, size_t actual_size);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);



/* global variables */
static char* heap_listp;    /* base of heap */




/*
 * add2list - adds free block to the appropriate segregated list
 *              by adding it to the front of the list as head &
 *              and linking it to the previous head
 */
static void add2list(char* bp, size_t size)
{
    /* address of head of a particular list */
    char* listhead;

    /* address pointing to the address of head of a particular list */
    char* start;

    if (size <= LIST1S){
        start = heap_listp + LIST1OS;
        listhead = (char*) GET(start);
            
    } else if (size <= LIST2S){
        start = heap_listp + LIST2OS;
        listhead = (char*) GET(start);   

    } else if (size <= LIST3S){
        start = heap_listp + LIST3OS;
        listhead = (char*) GET(start);

    } else if (size <= LIST4S){
        start = heap_listp + LIST4OS;
        listhead = (char*) GET(start);

    } else{
        start = heap_listp + LIST5OS;
        listhead = (char*) GET(start);

    }

    /* if no block in that size list */
    if (listhead == NULL){

        /* set free block's next and prev free block addresses to null */
        PUT(FREE_NEXT_ADD(bp), (size_t) NULL);
        PUT(FREE_PREV_ADD(bp), (size_t) NULL);

        /* set current block as head */
        PUT(start, (size_t) bp);

    /* if there're block(s) in size list */
    } else{

        /* set current free block's next pointer to previous head */
        PUT(FREE_NEXT_ADD(bp), (size_t) listhead);

        /* set current free block's prev pointer to null */
        PUT(FREE_PREV_ADD(bp), (size_t) NULL);

        /* set previous head's prev pointer to current free block */
        PUT(FREE_PREV_ADD(listhead), (size_t) bp);

        /* set current block as head */
        PUT(start, (size_t) bp);

    }


}




/*
 * remflist - removes free block from the appropriate segregated list
 *              by linking blocks to the left or right of it.  possibly
 *              updating initial list pointer to head of list.
 */
static void remflist(char* bp, size_t size)
{
    /* previous and next block's addresses */
    char* nextaddress;
    char* prevaddress;

    nextaddress = (char*) GET(FREE_NEXT_ADD(bp));
    prevaddress = (char*) GET(FREE_PREV_ADD(bp));

    
    /* if only free block in list, update head pointer to null */
    if (prevaddress == NULL && nextaddress == NULL){
        
        if (size <= LIST1S)
            PUT(heap_listp + LIST1OS, (size_t) NULL);
        else if (size <= LIST2S)
            PUT(heap_listp + LIST2OS, (size_t) NULL);
        else if (size <= LIST3S)
            PUT(heap_listp + LIST3OS, (size_t) NULL);
        else if (size <= LIST4S)
            PUT(heap_listp + LIST4OS, (size_t) NULL);
        else
            PUT(heap_listp + LIST5OS, (size_t) NULL);

    /* if head of list, update head pointer to next free block */
    } else if (prevaddress == NULL && nextaddress != NULL){
        
        /* update head pointer of segregated list */
        if (size <= LIST1S)
            PUT(heap_listp + LIST1OS, (size_t) nextaddress);
        else if (size <= LIST2S)
            PUT(heap_listp + LIST2OS, (size_t) nextaddress);
        else if (size <= LIST3S)
            PUT(heap_listp + LIST3OS, (size_t) nextaddress);
        else if (size <= LIST4S)
            PUT(heap_listp + LIST4OS, (size_t) nextaddress);
        else 
            PUT(heap_listp + LIST5OS, (size_t) nextaddress);

        /* update new head block's prev to null */
        PUT(FREE_PREV_ADD(nextaddress), (size_t) NULL);

    /* if tail of list w/more blocks in front, set prev's next to null */
    } else if (prevaddress != NULL && nextaddress == NULL){
        

        /* update new tail block's next to null */
        PUT(FREE_NEXT_ADD(prevaddress), (size_t) NULL);

    /* if in middle of a list, link blocks on both sides */
    } else{
        
        /* link previous block's next to current's next block */
        PUT(FREE_NEXT_ADD(prevaddress), (size_t) nextaddress);

        /* link next block's previous to current's previous block */
        PUT(FREE_PREV_ADD(nextaddress), (size_t) prevaddress);

    }
}


/*
 * extend_heap - extends the heap upward of size bytes
 * and adds free block to appropriate free list before
 * coalescing.
 */
static void* extend_heap(size_t size)
{
    void* bp;
    void* bpheader;


    if ((long) (bp = mem_sbrk(size)) < 0)
        return NULL;

    bpheader = HDRP(bp);

    /* Change epilogue header to new free block header */
    PUT4(bpheader, PACK(size, GET_PREV_ALLOC(bpheader)));

    /* set new free block footer */
    PUT4(FTRP(bp), GET4(bpheader));
    /* Add to segregated list */
    add2list(bp, size);

    /* set new epilogue header */
    PUT4(HDRP(NEXT_BLKP(bp)), 1);    


    /* coalesce free blocks if needed */
    return coalesce(bp);
}


/*
 * coalesce - combines free blocks from left and right with current
 *              free block to form larger free block.  removes current
 *              and/or left and/or right free blocks from their own lists
 *              and add to appropriate free list of new combined sizs.
 *              Called after each addition of a free block.
 */
static void* coalesce(void* bp)
{
    /* store prev and next block's info */
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    /* get size of current, prev, next free block (including header) */
    size_t size = GET_SIZE(HDRP(bp));
    size_t nsize = 0;
    size_t psize = 0;

    /* previous block's address and its header address */
    char* prev_hd;
    char* prev_blk;

    char* next_blk;

    /* 4 Cases */
    if (prev_alloc && next_alloc){   /* prev and next both allocated */   
        /* return current pointer to free block */
        return bp;
    }

    else if (prev_alloc && !next_alloc){    /* prev allocated, next free */
        next_blk = NEXT_BLKP(bp);

        nsize = GET_SIZE(HDRP(next_blk));

        /* remove current free block and next free block from lists */
        remflist(bp, size);
        remflist(next_blk, nsize);

        /* new block size is current free size plus next free size */ 
        size += nsize;

        /* change header to reflect new size */
        PUT4(HDRP(bp), PACK(size, prev_alloc));

        /* change footer to reflect new size */
        PUT4(FTRP(bp), GET4(HDRP(bp)));

        /* add new free block to segregated list */
        add2list(bp, size);

        /* return current pointer to free block 
        since block expanded to next */
        return bp;
    }

    else if (!prev_alloc && next_alloc){    /* prev free, next allocated */

        /* get previous block's location and header location */
        prev_blk = PREV_BLKP(bp);
        prev_hd = HDRP(prev_blk);

        psize = GET_SIZE(prev_hd);

        /* remove current free block and prev free block from lists */
        remflist(bp, size);
        remflist(prev_blk, psize);

        /* size is current free size plus prev free size */
        size += psize;

        /* change header to reflect new size */
        PUT4(prev_hd, 
            PACK(size, 
                GET_PREV_ALLOC(prev_hd)));

        /* change footer to reflect new size */
        PUT4(FTRP(prev_blk), GET4(prev_hd));

        /* add new free block to segregated list */
        add2list(prev_blk, size);        

        /* return prev pointer to prev block 
        since block expanded to prev */
        return prev_blk;
    }

    else{                                       /* prev free, next free */

        /* get previous block's location and header location */
        prev_blk = PREV_BLKP(bp);
        prev_hd = HDRP(prev_blk);

        next_blk = NEXT_BLKP(bp);        
        
        psize = GET_SIZE(prev_hd);
        nsize = GET_SIZE(HDRP(next_blk));

        /* remove current, prev, and next free block from lists */
        remflist(bp, size);
        remflist(prev_blk, psize);
        remflist(next_blk, nsize);

        /* size is current free plus prev free and next free size */
        size += psize + nsize;


        /* change header to reflect new size */
        PUT4(prev_hd,
            PACK(size,
                GET_PREV_ALLOC(prev_hd)));

        /* change footer to reflect new size */
        PUT4(FTRP(prev_blk), GET4(prev_hd));

        /* add new free block to segregated list */
        add2list(prev_blk, size);

        /* return prev pointer to free block 
        since block expanded to prev */
        return prev_blk;
    }

}


/*
 * mm_init - initializes the heap by storing pointers to 
 * start of each free list at beginning of heap as well as
 * creating the initial prologue and eplilogue blocks.
 * The heap is also initially extended to CHUNKSIZE bytes.
 */
int mm_init(void) {
    char* heap_start;

    /* allocate segregated free list pointers on heap */
    if ((heap_listp = mem_sbrk(TOTALLIST*DSIZE)) == NULL)
        return -1;

    /* create prologue and epilogue */
    if ((heap_start = mem_sbrk(4*WSIZE)) == NULL)
        return -1;
    PUT4(heap_start, 0);
    PUT4(heap_start + WSIZE, PACK(OVERHEAD, 1));
    PUT4(heap_start + DSIZE, PACK(OVERHEAD, 1));
    PUT4(heap_start + WSIZE + DSIZE, 
            PACK(0, PREVALLOC|CURRALLOC));

    /* initialize segregated list pointers */
    PUT(heap_listp + LIST1OS, (size_t) NULL);
    PUT(heap_listp + LIST2OS, (size_t) NULL);
    PUT(heap_listp + LIST3OS, (size_t) NULL);
    PUT(heap_listp + LIST4OS, (size_t) NULL);
    PUT(heap_listp + LIST5OS, (size_t) NULL);

    /* create initial empty space of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;

	return 0;
}



/*
 * find - find searches through a particular size free list
 * to find a possible free block >= size requested and returns
 * pointer to a possible free block or NULL if none are found.
 */
static void* find(size_t start_size, size_t actual_size)
{
    char* current = NULL;

    /* determine which list to peruse */
    if (start_size == I1OS)
        current = (char*) GET(heap_listp + LIST1OS);
    else if (start_size == I2OS)
        current = (char*) GET(heap_listp + LIST2OS);
    else if (start_size == I3OS)
        current = (char*) GET(heap_listp + LIST3OS);
    else if (start_size == I4OS)
        current = (char*) GET(heap_listp + LIST4OS);
    else if (start_size == I5OS)
        current = (char*) GET(heap_listp + LIST5OS);
    

    /* finding available free block in list */
    while (current != NULL){
        if (actual_size <= GET_SIZE(HDRP(current))){
            break;
        }
        current = (char*) GET(FREE_NEXT_ADD(current));
    }   

    return current;
}




/*
 * find_fit - searches through all free lists containing
 * blocks with size greater than size requested and returns
 * pointer to a satisfacotry free block or NULL if none 
 * are found. 
 */
static void* find_fit(size_t asize)
{
    size_t start_size;
    char* bp = NULL;


    /* size breakdown */
    if (asize <= LIST1S){
        for (start_size = I1OS; start_size < TOTALLIST; start_size++){
            if ((bp = find(start_size, asize)) != NULL)
                return bp;
        }
    } else if (asize <= LIST2S){
        for (start_size = I2OS; start_size < TOTALLIST; start_size++){
            if ((bp = find(start_size, asize)) != NULL)
                return bp;
        }
    } else if (asize <= LIST3S){
        for (start_size = I3OS; start_size < TOTALLIST; start_size++){
            if ((bp = find(start_size, asize)) != NULL)
                return bp;
        }
    } else if (asize <= LIST4S){
        for (start_size = I4OS; start_size < TOTALLIST; start_size++){
            if ((bp = find(start_size, asize)) != NULL)
                return bp;
        }
    } else{
        start_size = I5OS;
        if ((bp = find(start_size, asize)) != NULL){
            return bp;
        }
    }
    
    return bp;
}




/*
 * place - allocates block of memory at address bp. if remaining
 *          memory is >= min free block size, allocate requested
 *          amount and form new free block to add to segregated
 *          list.  if not, allocate entire block of memory at
 *          address bp.
 */
static void place(void* bp, size_t asize)
{

    /* original free block size */
    size_t freesize = GET_SIZE(HDRP(bp));
    /* remaining free block size */
    size_t remainsize = freesize - asize;

    /* header of current bp */
    char* bpheader = HDRP(bp);
    /* next adjacent block address */
    char* nextaddress = NEXT_BLKP(bp);    


    /* remove free block from list */
    remflist(bp, freesize);   


    /* if what remains is larger than min block size of 24 bytes 
        will form new free block */
    if (remainsize >= MINBLOCK){

        /* update new header information, store info bits */
        PUT4(HDRP(bp), 
            PACK(asize, 
                GET_PREV_ALLOC(bpheader) | CURRALLOC));

        /* update next block's address to remaining free block's address */
        nextaddress = NEXT_BLKP(bp);        
        

        /* inform next adjacent free block that its previous block 
            is allocated */
        PUT4(HDRP(nextaddress), remainsize|PREVALLOC);
        PUT4(FTRP(nextaddress), remainsize|PREVALLOC);

        /* add remaining free block to appropriate segregated list */
        add2list(nextaddress, remainsize); 

    /* if what remains isn't larger than min block, then assign 
        entire free block to allocated */
    } else{

        /* update new header information, store info bits */
        PUT4(HDRP(bp),
            PACK(freesize,
                GET_PREV_ALLOC(bpheader)|
                CURRALLOC));

        /* inform next adjacent block that its previous block 
            is allocated */
        PUT4(HDRP(nextaddress), GET4(HDRP(nextaddress))|PREVALLOC);

        /* update next adjacent block's footer only if free */
        if (!GET_ALLOC(HDRP(nextaddress)))
            PUT4(FTRP(nextaddress), GET4(HDRP(nextaddress)));

    }
}



/*
 * malloc - returns a pointer to an allocated block payload 
 * of at least size bytes.  It first searches through different
 * size free lists for a free block and if needed, extend the 
 * heap.
 */
void *malloc (size_t size) {

    size_t asize;       /* adjusted block size */
    size_t extendsize;  /* size to be extended */
    char* bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include header and alignment requests */    
    if (size <= 2*DSIZE)
        asize = MINBLOCK;
    else
        asize = ALIGN(size + WSIZE);

    /* search through heap for possible fit */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);   /* actual assignment */
        return bp;
    }

    /* If no fit, get more memory and allocate memory */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    place(bp, asize);   /* assignment */

    return bp;
}

/*
 * free - frees the block pointed to by ptr and returns 
 * nothing.  It adds free'd block to apprpriate size
 * free list afterwards.
 */
void free (void *ptr) {

    char* hdptr;
    size_t size;
    char* nextblk;
    char* hdnextblk; 
    
    if (ptr == NULL)
        return;

    hdptr = HDRP(ptr);
    size = GET_SIZE(hdptr);
    nextblk = NEXT_BLKP(ptr);
    hdnextblk = HDRP(nextblk);

    /* update header and footer to unallocated */
    PUT4(hdptr, size|GET_PREV_ALLOC(hdptr));
    PUT4(FTRP(ptr), GET4(hdptr));


    /* update next block, its previous is no longer allocated */
    PUT4(hdnextblk, 
            GET_SIZE(hdnextblk)|
            GET_ALLOC(hdnextblk));

    if (!GET_ALLOC(hdnextblk))
            PUT4(FTRP(nextblk), GET4(hdnextblk));    
    
    /* add free block to appropriate segregated list */
    add2list(ptr, size);

    coalesce(ptr);
}

/*
 * realloc - Returns a pointer to an allocated region
 * of at least size bytes with the contents of pointer
 * oldptr up to the size bytes. The default action is to
 * simply free current allocated block and copy size bytes
 * at oldptr to a new free block and free oldptr.
 */
void *realloc(void *oldptr, size_t size) {

    /* new malloc'd address of size size*/
    char* newadd;

    /* size to be copied */
    size_t cpsize;


    /* if ptr is NULL, call equivalent to malloc(size) */
    if (oldptr == NULL)
        return malloc(size);

    /* if size = 0, call equivalanet to free(oldptr), returns null */
    if (size == 0){
        free(oldptr);
        return NULL;
    }
        
    /* else, allocate new free block, copy old content over */
    newadd = malloc(size);
    cpsize = MIN(size, GET_SIZE(HDRP(oldptr)) - WSIZE);

    /* move from source to dest */
    memmove(newadd, oldptr, cpsize);

    /* free old block */
    free(oldptr);    

	return newadd;
}


/*
 * calloc - Allocates memory for an array of nmemb elements 
 * of size bytes each and returns a pointer to the allocated 
 * memory. The memory is set to zero before returning.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t tsize = nmemb*size;
    char* ptr = malloc(tsize);

    char* temp = ptr;
    size_t i;

    for (i = 0; i < nmemb; i++){
        *temp = 0;
        temp = temp + size;
    }

    return ptr;
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
	return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
	return (size_t)ALIGN(p) == (size_t)p;
}


/*
 * mm_checkheap - scans the heap and checks it 
 * for consistency.
 *
 * Invariants:
 *      
 *      - all blocks are aligned to 8 bytes (checked)
 *      - all blocks store info if previous
 *          block is allocated
 *      - all free blocks' headers/footers
 *          are the same (checked)
 *      - each free list contains only blocks 
 *          within size ranges (checked)
 *      - each block is within the heap (checked)
 *      - no consecutive free blocks (checked)
 */
void mm_checkheap(int verbose) {
    
    /* pointer to very first block */
    char* ptr = heap_listp + TOTALLIST*DSIZE + DSIZE + DSIZE;

    /* for testing if block falls under appropriate size list */
    char* listptr = NULL;
    unsigned minbsize = 0;
    unsigned maxbsize = 0;
    unsigned start_size = 0;


    /* check if all blocks in each freelist fall within
        appropriate ranges */
    for (start_size = I1OS; start_size < TOTALLIST; start_size++){
        if (start_size == I1OS){
            listptr = (char*) GET(heap_listp + LIST1OS);
            minbsize = 0;
            maxbsize = LIST1S;
        } else if (start_size == I2OS){
            listptr = (char*) GET(heap_listp + LIST2OS);
            minbsize = LIST1S;
            maxbsize = LIST2S;
        } else if (start_size == I3OS){
            listptr = (char*) GET(heap_listp + LIST3OS);
            minbsize = LIST2S;
            maxbsize = LIST3S;
        } else if (start_size == I4OS){
            listptr = (char*) GET(heap_listp + LIST4OS);
            minbsize = LIST3S;
            maxbsize = LIST4S;
        } else{
            listptr = (char*) GET(heap_listp + LIST5OS);
            minbsize = LIST4S;
            maxbsize = ~0;
        }

        while (listptr != NULL){
            if (!(minbsize < GET_SIZE(HDRP(listptr)) &&
                GET_SIZE(HDRP(listptr)) <= maxbsize)){
                printf("free block pointer %p \
isn't in appropriate list", listptr);
            }
            listptr = (char*) GET(FREE_NEXT_ADD(listptr));
        }

    }


    /* traverse through entire heap */
    while((GET4(HDRP(ptr)) != 1) && (GET4(HDRP(ptr)) != 3)){

        /* for all blocks, check for:
            1. alignment
            2. existence in heap
        */
        if (!aligned(ptr)){
            printf("block pointer %p isn't aligned\n", ptr);            
        }
        if (!in_heap(ptr)){
            printf("block pointer %p isn't in heap\n", ptr);
        }


        /* if block is free, check for:
            1. header/footer mismatch
            2. adjacent free blocks
            3. next/prev free pointer inconsistencies
        */ 
        if (!GET_ALLOC(HDRP(ptr))){

            if ((GET4(HDRP(ptr)) != GET4(FTRP(ptr))))
                printf("free block pointer %p \
header and footer mismatch\n", ptr);

            if ((GET4(HDRP(NEXT_BLKP(ptr))) != 1) &&
                (GET4(HDRP(NEXT_BLKP(ptr))) != 3) &&
                !GET_ALLOC(HDRP(NEXT_BLKP(ptr))))
                printf("free block pointer %p \
and %p are adjacent\n", ptr, NEXT_BLKP(ptr));     

            if ((char*) GET(FREE_NEXT_ADD(ptr)) != NULL && 
                (char*) GET(FREE_PREV_ADD(GET(FREE_NEXT_ADD(ptr)))) != ptr)
                printf("free block pointer %p's \
next pointer is inconsistent\n", ptr);      

           if ((char*) GET(FREE_PREV_ADD(ptr)) != NULL &&
                (char*) GET(FREE_NEXT_ADD(GET(FREE_PREV_ADD(ptr)))) != ptr)
                printf("free block pointer %p's \
previous pointer is inconsistent\n", ptr);
        }


        /* extra info printed for every block even with no 
            apparent error */
        if (verbose){

            printf("\nblock pointer: %p\n", ptr);            
            printf("block size: %d\n", GET_SIZE(HDRP(ptr)));            

            if (GET_ALLOC(HDRP(ptr)))
                printf("block is allocated\n");
            else
                printf("block is free\n");
            
            if (verbose > 1){
                if (GET_PREV_ALLOC(HDRP(ptr)))
                    printf("previous block is allocated\n");
                else
                    printf("previous block is free\n");                
            }            
        }        

        ptr = NEXT_BLKP(ptr);
    }
    
}
