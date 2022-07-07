#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;


/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);
static int get_index_sz(header* block);
// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t object_left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);
static inline header*  coalesce(header * block);
static void coalesce_left(header* block);
static void  coalesce_right(header* block);
// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);
static inline header * find_allocable(size_t aligned_size);
static inline header * handle_chunk(header * chunk);

static header* find_next_fp(header* lfp);
// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_object_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->object_left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param object_left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t object_left_size) {
	set_object_state(fp,FENCEPOST);
	set_object_size(fp, ALLOC_HEADER_SIZE);
	fp->object_left_size = object_left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_object_state(hdr, UNALLOCATED);
  set_object_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->object_left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
  if(raw_size == 0) return;
  size_t  aligned_size =  raw_size % 8 == 0  ? raw_size : (raw_size + (8 - (raw_size % 8))); //for use when finding the blo
  size_t actual_size = aligned_size + ALLOC_HEADER_SIZE;//for use when calculating split
  actual_size = actual_size >= UNALLOC_HEADER_SIZE ? actual_size : UNALLOC_HEADER_SIZE;
 /* above ensures that block never hits the zero index which is always empty (due to next & prev) */

  header* allocable_block = find_allocable(aligned_size);

  if(allocable_block == NULL){
    /*TODO implement sbrk alloc */
    header* new_chunk = allocate_chunk(ARENA_SIZE);
    if(new_chunk == NULL){
     errno = ENOMEM;
     return NULL;
    }
    new_chunk = handle_chunk(new_chunk);
    if(new_chunk->prev == NULL || new_chunk->next == NULL){
         
      insert_unallocated(new_chunk);
    }

    allocable_block = allocate_object(aligned_size);
    return allocable_block;
  }
  size_t block_actual_size = get_object_size(allocable_block); 
  size_t block_free_size = block_actual_size - ALLOC_HEADER_SIZE;//free memory availble for allocation
 
  if(block_free_size - aligned_size < UNALLOC_HEADER_SIZE){ //checks if left over free memory is large enough to support UNALLOC_HEADER_SZ
     remove_block(allocable_block);
     set_object_state(allocable_block, ALLOCATED);
     return allocable_block->data;
  }
  else {
    int index = get_index_sz(allocable_block);
    size_t offset = block_actual_size - actual_size;
    header * right_split = (header *) ((char *) allocable_block + offset); //the block to be used for allocation
    header * right_adj = (header *) ((char*) allocable_block + get_object_size(allocable_block)); // the block to the right of the block used for allocation
    int new_index;
    right_adj->object_left_size = actual_size; 
    /*block used for allocation's neighbor updated left size */
    set_object_size(right_split,actual_size);
    right_split->object_left_size = offset;
    set_object_size(allocable_block,offset); 
    new_index = get_index_sz(allocable_block);
   
    if(new_index != index){
       remove_block(allocable_block);
       insert_unallocated(allocable_block);
    }

    set_object_state(right_split,ALLOCATED);  
    return right_split->data;
  
  }
  
}

static inline contiguous(header* chunk){
   return (header*) ((char*) lastFencePost + ALLOC_HEADER_SIZE) == (header*) ((char*) chunk - ALLOC_HEADER_SIZE);
}

static header* chunk_coalesce(header* chunk){

  size_t new_size = get_object_size(chunk) +( 2 * ALLOC_HEADER_SIZE); //assumes that there is always 2 fence posts

  chunk = (header*) ((char*) chunk - (2*ALLOC_HEADER_SIZE)); //gives me newchunk + 2 fence posts to the left
  set_object_size(chunk, new_size);

  header* right_fencepost = (header*) ((char*) chunk + new_size); 
  right_fencepost->object_left_size = new_size;

  set_object_state(chunk,UNALLOCATED);
  chunk->next = NULL;
  chunk->prev = NULL;

  return coalesce(chunk);  
}
static inline header* handle_chunk(header * chunk){ 


  if(contiguous(chunk)){
    chunk = chunk_coalesce(chunk);
    remove_block(chunk);
    lastFencePost = (header*) ((char*) chunk + get_object_size(chunk));
    return chunk;
  }
  
  lastFencePost = (header*) ((char*) chunk + get_object_size(chunk));
  insert_os_chunk((header*) ((char*) chunk - ALLOC_HEADER_SIZE));
  return chunk;  

}
void remove_block(header* block){
 if(block->prev == NULL || block->next == NULL) return;
 header* temp_prev = block->prev;
 header* temp_next = block->next;
 temp_prev->next = temp_next;
 temp_next->prev = temp_prev;
 block->prev = NULL;
 block->next = NULL;

}
 void insert_unallocated(header* new_block){
  
   size_t new_size = get_object_size(new_block) - UNALLOC_HEADER_SIZE;
   int index = (new_size / 8) + 1; // would this be sz/8  - 1?
   index = index < N_LISTS ? index : (N_LISTS - 1);
   header* sentinel = &freelistSentinels[index];
 
  //linked list insertion
   if(sentinel->next == sentinel){
     sentinel->next = new_block;
     new_block->prev = sentinel;
     new_block->next = sentinel;
     sentinel->prev = new_block;
     return;
   }
   header *temp = sentinel->next;
   new_block->next = temp;
   sentinel->next = new_block;
   new_block->prev = sentinel;
   temp->prev = new_block; //updates the newblocks neighbor's prev ptr
   
}

header* find_allocable(size_t aligned_size){
   size_t actual_size = aligned_size+ ALLOC_HEADER_SIZE;
   int request_index = aligned_size/8 < N_LISTS? (aligned_size/8) - 1 : N_LISTS-1;
   request_index = actual_size < UNALLOC_HEADER_SIZE ? 1 : request_index; 
   header* maxSentinel = &freelistSentinels[N_LISTS-1];

   for(int i = request_index; i < N_LISTS- 1; i++){
       header* sentinel = &freelistSentinels[i];
       if (sentinel == sentinel->next){
          continue;
       }
       else{  
         return sentinel->next;
       }    
   }
   //overflow region
   header* cur = maxSentinel->next;
   while(cur != maxSentinel){
      if(get_object_size(cur) >= actual_size){
         return cur;
      }
      cur = cur->next;
   }
   return NULL;

}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  if(!p) return; 
  header * block = (header *) ((char *) p - ALLOC_HEADER_SIZE);
  assert(get_object_state(block) != FENCEPOST);
  if(get_object_state(block) == UNALLOCATED){
   fprintf(stderr,"Double Free Detected\n");
   assert(false);
  }

  set_object_state(block, UNALLOCATED);
  block = coalesce(block);
  if(block->prev == NULL || block->next == NULL){
    insert_unallocated(block);   
  }
 
}


static int get_index_sz(header* block){
   int size = get_object_size(block) - UNALLOC_HEADER_SIZE;
   int index = (size/8) + 1;
   index = index < N_LISTS ? index :( N_LISTS - 1);
   return index;
}
static void coalesce_left(header* block){
  header* left_block = (header*) ((char*) block - block->object_left_size);
  int og_left_index = get_index_sz(left_block);
  header* right_block = (header*) ((char*) block + get_object_size(block));
  int new_left_index;
  
  set_object_size(left_block, get_object_size(block) + block->object_left_size);
  right_block->object_left_size = get_object_size(left_block);
  
  new_left_index = get_index_sz(left_block);
  if(new_left_index != og_left_index){
   remove_block(left_block);
  }
  return;
}

static void coalesce_right(header* block){
  header* right_block = (header*) ((char*) block + get_object_size(block));
  header* right_right_block = (header*) ((char*) right_block + get_object_size(right_block));
  int og_right_index = get_index_sz(right_block);
  int new_right_index;
 
  og_right_index = og_right_index < (N_LISTS - 1) ? og_right_index : -1;
  set_object_size(block,get_object_size(block) + get_object_size(right_block));
  right_right_block->object_left_size = get_object_size(block);
  
  block->prev = right_block->prev;
  block->next = right_block->next;
  
  new_right_index = get_index_sz(block);
  
  if(new_right_index != og_right_index){
   remove_block(right_block);
   remove_block(block);
  }
  
  return; 
  
}

static inline header *  coalesce(header * block){ 
  size_t left_size = block->object_left_size;
  size_t size = get_object_size(block);
  block->prev = NULL;
  block->next = NULL; 
 
  header * left_block = (header *) ((char *) block - left_size);
  header * right_block = (header *) ((char *) block + size);

  if( get_object_state(right_block) == UNALLOCATED){
    coalesce_right(block);
  }
  if( get_object_state(left_block) == UNALLOCATED){
    coalesce_left(block);
    block = left_block; 
  }
  return block;
   
}
/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_object_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_object_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_object_size(chunk)  != get_right_header(chunk)->object_left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_object_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
