#include "seahorn/seahorn.h"
#include <stdarg.h>
#include <cstdint>
#include <cstdio>
#undef NDEBUG
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <map>
#include <functional>
#include <stddef.h>

extern "C" {

void sealog (const char *format, ...) {
    va_list args;
    va_start(args, format);
    if (std::getenv("SEAHORN_RT_VERBOSE"))
        vprintf(format, args);
    va_end(args);
}

void __VERIFIER_error() {
  printf("[sea] __VERIFIER_error was executed\n");
  exit(1);
}

void __VERIFIER_assume(bool x) {
  assert(x);
}

bool __seahorn_get_value_i1(int ctr, bool *g_arr, int g_arr_sz) {
  sealog("[sea] __seahorn_get_value_i1(%d, %d)\n", ctr, g_arr_sz);
  if (ctr >= g_arr_sz) {
    sealog("\tout-of-bounds index\n");
    return 0;
  } else {
    return g_arr[ctr];
  }
}

#define get_value_helper(ctype, llvmtype)                               \
  ctype __seahorn_get_value_ ## llvmtype (int ctr, ctype *g_arr, int g_arr_sz) { \
    sealog("[sea] __seahorn_get_value_(" #llvmtype ", %d, %d)\n", ctr, g_arr_sz); \
    if (ctr >= g_arr_sz) {						\
      sealog("\tout-of-bounds index\n");				\
      return 0;								\
    }									\
    else { 								\
      return g_arr[ctr];						\
    }									\
  }

#define get_value_int(bits) get_value_helper(int ## bits ## _t, i ## bits)

get_value_int(64)
get_value_int(32)
get_value_int(16)
get_value_int(8)

get_value_helper(intptr_t, ptr_internal)

const int MEM_REGION_SIZE_GUESS = 4000;
const int TYPE_GUESS = sizeof(int);

std::map<intptr_t, intptr_t, std::greater<intptr_t>> absptrmap;

std::map<size_t, size_t, std::greater<size_t>> fatptrslot0; // (int)ptr : base
std::map<size_t, size_t, std::greater<size_t>> fatptrslot1; // (int)ptr : size

// 64-bit fat pointer: [8:base|8:size|48:addr]
static uint16_t ptr_base; // 16 bit common base of stack allocated ptrs
static bool ptr_base_set = false;

// Hook for gdb-like tools: do nothing here.
void* __emv(void* p) {
  return p;
}
  
  /*intptr_t __seahorn_get_value_ptr(int ctr, intptr_t *g_arr, int g_arr_sz, int ebits) {
  static std::unordered_map<intptr_t, intptr_t> absptrmap;
  intptr_t absptr = __seahorn_get_value_ptr_internal(ctr, g_arr, g_arr_sz);

  auto concptrfind = absptrmap.find(absptr);
  intptr_t concptr;
  if (concptrfind == absptrmap.end()) {
    concptr = (intptr_t) calloc(MEM_REGION_SIZE_GUESS, ebits == 0 ? TYPE_GUESS : ebits);
    absptrmap.insert({absptr, concptr});
  } else {
    concptr = concptrfind->second;
  }

  printf("Returning %#lx for abstract pointer %#lx\n", concptr, absptr);

  return concptr;
  }*/

  intptr_t __seahorn_get_value_ptr(int ctr, intptr_t *g_arr, int g_arr_sz, int ebits) {
    intptr_t absptr = __seahorn_get_value_ptr_internal(ctr, g_arr, g_arr_sz);

    size_t sz = MEM_REGION_SIZE_GUESS * (ebits == 0 ? TYPE_GUESS : ebits);

    absptrmap[absptr] = absptr + sz;

    sealog("[sea] returning a pointer to an abstract region [%#lx, %#lx]\n", absptr, absptrmap.at(absptr));

    return absptr;
  }

  bool is_dummy_address (void *addr) {

    intptr_t ip = intptr_t (addr);
    auto it = absptrmap.lower_bound (ip+1);
    if (it == absptrmap.end()) return false;
    intptr_t lb = it->first;
    intptr_t ub = it->second;

    return (ip >= lb && ip < ub);
  }

  bool is_legal_address (void *addr) {
    return (! is_dummy_address (addr) &&
	    (size_t(addr) >= 0x100000 &&
	     size_t(addr) <= 0xFFFFFFFFFFFF));
  }

/** Dummy implementation of memory wrapping functions */
void __seahorn_mem_alloc(void* start, void* end, int64_t val, size_t sz)
{}

void __seahorn_mem_init (void* addr, int64_t val, size_t sz)
{}

void __seahorn_mem_store (void *src, void *dst, size_t sz)
{
  sealog("[sea] __seahorn_mem_store from %p to %p\n", src, dst);
  if (is_legal_address (dst) && is_legal_address(src)) {
  /* if dst is a legal address */
    sealog("\tmemory write ");
    memcpy (dst, src, sz);
    sealog("done\n");
  }
  /* else if dst is illegal, do nothing */
  else{
    sealog("\tignoring write to illegal memory address\n");
  }
}

void __seahorn_mem_load (void *dst, void *src, size_t sz)
{
  sealog("[sea] __seahorn_mem_load from %p to %p\n", src, dst);
  if (is_legal_address (src) && is_legal_address(dst)) {
  /* if src is a legal address */
    sealog("\tmemory read ");
    memcpy (dst, src, sz);
    sealog("done\n");
  }
  /* else, if src is illegal, return a dummy value */
  else {
    sealog("\tignoring read from an illegal memory address\n");
    bzero(dst, sz);
  }
}

// Dummy klee_make_symbolic function
void klee_make_symbolic(void *v, size_t sz, char *fname) {
  sealog("[sea] calling klee_make_symbolic for %s\n", fname);
}

void klee_assume(int b) {
  sealog("[sea] calling klee_assume\n");
  __VERIFIER_assume (b);
}

void __assert_fail (const char * assertion, const char * file,
		    unsigned int line, const char * function) {
  printf("[sea] exiting with a call to __assert_fail %s\n",assertion);
  exit(1);
}

// draft
void* __sea_set_extptr_slot0_fp(void* ptr, size_t base) {
  if (!ptr_base_set) {
    ptr_base_set = true;
    ptr_base = (uint16_t)((size_t)ptr >> 48);
  }
  size_t base_bits = (size_t)base & 0xff;
  size_t packed = (base_bits << 56) | (size_t)ptr;
  return (void*)packed;
}

// draft
void* __sea_set_extptr_slot1_fp(void* ptr, size_t size) {
  if (!ptr_base_set) {
    ptr_base_set = true;
    ptr_base = (uint16_t)((size_t)ptr >> 48);
  }
  assert(size < 512);
  size_t packed = (size << 48) | (size_t)ptr;
  return (void*)packed;
}

// draft
void* __sea_recover_pointer_fp(void* cooked) {
  size_t cleared = (size_t) cooked & 0xffffffffffff;
  size_t recov = cleared | (size_t) ptr_base << 48;
  return (void*) recov;
}

// draft
size_t __sea_get_extptr_slot0_fp(void *ptr) {
  size_t raw = (size_t)ptr >> 56; // 8 bits stored only
  void* recov = __sea_recover_pointer_fp(ptr);
  size_t recov_base = (size_t)recov & 0xffffffffffffff00;
  return recov_base | raw;
}

// draft
size_t __sea_get_extptr_slot1_fp(void *ptr) {
  size_t info_bits = (size_t)ptr >> 48;
  return info_bits & 0xff;
}

// draft
void* __sea_copy_extptr_slots_fp(void *dst, void*src) {
  size_t src_info = (size_t)src & 0xffff000000000000;
  size_t dst_addr = (size_t)dst & 0xffffffffffff;
  return (void*)(src_info | dst_addr);
}

void* __sea_set_extptr_slot0_hm(void* ptr, size_t base) {
  fatptrslot0[(size_t)ptr] = (size_t)base;
  return ptr;
}

void* __sea_set_extptr_slot1_hm(void *ptr, size_t size) {
  fatptrslot1[(size_t)ptr] = (size_t)size;
  return ptr;
}

void* __sea_recover_pointer_hm(void* cooked) {
  return cooked;
}

size_t __sea_get_extptr_slot0_hm(void *ptr) {
  assert(fatptrslot0.count((size_t)ptr) != 0);
  return (size_t)fatptrslot0[(size_t)ptr];
}

size_t __sea_get_extptr_slot1_hm(void *ptr) {
  assert(fatptrslot1.count((size_t)ptr) != 0);
  return fatptrslot1[(size_t)ptr];
}

void* __sea_copy_extptr_slots_hm(void *dst, void *src) {
  assert(fatptrslot0.count((size_t)src) != 0 && fatptrslot1.count((size_t)src) != 0);
  size_t dst_int = (size_t)dst;
  size_t src_int = (size_t)src;
  fatptrslot0[dst_int] = fatptrslot0[src_int];
  fatptrslot1[dst_int] = fatptrslot1[src_int];
  return dst;
}

}
