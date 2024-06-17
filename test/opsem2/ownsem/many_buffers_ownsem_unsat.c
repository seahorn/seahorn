// RUN: %sea -m64 -DOWNSEM_BORCHK -O3 --inline --no-lower-gv-init-struct --horn-bv2-tracking-mem --horn-unify-assumes=true --horn-gsa --no-fat-fns=bcmp,memcpy,assert_bytes_match,ensure_linked_list_is_allocated,sea_aws_linked_list_is_valid --dsa=sea-cs-t --devirt-functions=sea-dsa --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=true --horn-bmc-coi=true --sea-opsem-allocator=static --horn-explicit-sp0=false --horn-bv2-lambdas --horn-bv2-simplify=true --own-sem "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

extern void sea_set_shadowmem(char, char*, size_t);
extern size_t sea_get_shadowmem(char, char*);
extern void sea_tracking_on();
extern void sea_tracking_off();
extern bool nd_bool();
extern size_t nd_size_t();
#define ND __declspec(noalias)
extern ND void memhavoc(void *ptr, size_t size);

#define MAX_BUFS 30
static size_t buffer_counter = 0;

typedef struct buf {
    char *data;
    size_t len;    
} Buffer;

void inline process_buffer(char *buffer, size_t len ) {
  memhavoc(buffer, len);
  size_t counter = sea_get_shadowmem(TRACK_CUSTOM0_MEM, buffer);
  size_t cache_counter;
  SEA_READ_CACHE(cache_counter, buffer);
  SEA_WRITE_CACHE(buffer, cache_counter + buffer_counter);
  sea_set_shadowmem(TRACK_CUSTOM0_MEM, buffer, counter + buffer_counter);
  buffer_counter = buffer_counter + 1;   
  SEA_DIE(buffer);
}

int main(int argc, char **argv) {
  sea_tracking_on();
  Buffer bufs[MAX_BUFS];
  for(int i =0;i < MAX_BUFS; i++) {
    size_t buf_size = nd_size_t();
    assume(buf_size < 4096);
    bufs[i].data = (char *) malloc(buf_size);
    SEA_MKOWN(bufs[i].data);
    bufs[i].len = buf_size;
    SEA_WRITE_CACHE(bufs[i].data, 1);
    sea_set_shadowmem(TRACK_CUSTOM0_MEM, bufs[i].data, 1);
  }  

  size_t choice1 = nd_size_t();
  size_t choice2 = nd_size_t();
  assume(choice1 < MAX_BUFS);
  assume(choice2 < MAX_BUFS);
  assume(choice1 != choice2);
  char *bor_data;
  SEA_BORROW(bor_data, bufs[choice1].data);
  process_buffer(bor_data, bufs[choice1].len);  
  SEA_BORROW(bor_data, bufs[choice2].data);
  process_buffer(bor_data, bufs[choice2].len); 
  size_t cache_counter1, cache_counter2;
  SEA_READ_CACHE(cache_counter1, bufs[choice1].data);
  SEA_READ_CACHE(cache_counter2, bufs[choice2].data);
  size_t counter1 = sea_get_shadowmem(TRACK_CUSTOM0_MEM, bufs[choice1].data);  
  size_t counter2 = sea_get_shadowmem(TRACK_CUSTOM0_MEM, bufs[choice2].data);  
  sassert(cache_counter1 + 1 == cache_counter2);
  // sassert(counter1 + 1 == counter2);
  // sassert(bufs[choice1].data[0] + 1  == bufs[choice2].data[0]);
  sea_tracking_off();
  return 0;
}
