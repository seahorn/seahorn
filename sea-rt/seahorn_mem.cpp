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
#include <stdint.h>
#include <inttypes.h>

extern "C" {

typedef uint64_t sea_addr_t;
  
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

void __VERIFIER_assume(int x) {
  assert(x);
}

void __SEA_assume(bool x) {
  assert(x);
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

std::map<intptr_t, intptr_t, std::greater<intptr_t>> absptrmap;
std::map<intptr_t, void*> abs_to_concr_ptr_map;

intptr_t __seahorn_get_value_ptr(int ctr, intptr_t *g_arr, int g_arr_sz, int ebits) {
    intptr_t absptr = __seahorn_get_value_ptr_internal(ctr, g_arr, g_arr_sz);
    sealog("[sea] returning a pointer %#lx to an abstract region\n", absptr);
    return absptr;
}
  
/** Implementations of the memory wrapping functions */

intptr_t __seahorn_get_abs_base_address (void *addr) {
  intptr_t ip = intptr_t (addr);
  auto it = absptrmap.lower_bound (ip+1);
  if (it == absptrmap.end()) return false;
  intptr_t lb = it->first;
  intptr_t ub = it->second;
  if (ip >= lb && ip < ub) {
    return lb;
  } else {
    return 0;
  }
}

/* Hook for gdb-like tools */  
void* __emv(void* p) {
  if (intptr_t ab = __seahorn_get_abs_base_address(p)) {
    auto it = abs_to_concr_ptr_map.find((intptr_t) ab);
    if (it != abs_to_concr_ptr_map.end()) {
      intptr_t pb =  (intptr_t) it->second;
      intptr_t offset = ((intptr_t) p - ab);
      return (void*) (pb + offset);
    }
  }
  printf("Address %#lx not found in the emv map\n", (intptr_t) p);
  return p;
}
  
void __seahorn_mem_alloc(void* start, void* end, int64_t val, size_t sz){
  intptr_t startp = (intptr_t) start;
  intptr_t endp = (intptr_t) end;  
  ptrdiff_t n = endp - startp;
  sealog("[sea] __seahorn_mem_alloc [%#lx,%#lx] of %td bytes and sz=%d\n",
	 startp, endp, n, sz);
  
  if (n <= 0) {
    printf("[sea] exiting because of negative size.\n");
    exit(1);
  }
  void*p = malloc(n);
  if (!p) {
    printf("[sea] failed to allocate %td bytes.\n",n);
    exit(1);
  }

  //int64_t* ip = (int64_t*) p;
  for (unsigned i=0; i < (n/sz) ; ++i) {
    memcpy((void*) ((intptr_t) p + (i*sz)), &val, sz);
    //ip[i] = val;
  }
  
  
  absptrmap[startp] = endp;  
  abs_to_concr_ptr_map[startp] = p;
  sealog("\tInitialized the whole region to %#lx (%td)\n",
	 (intptr_t) val, (intptr_t) val);
  sealog("\tMap abstract %#lx to physical %#lx\n",startp, (intptr_t) p);  
}

void __seahorn_mem_init (void* addr, int64_t val, size_t sz) {
  sealog("[sea] __seahorn_mem_init %p with %#lx (%td) and sz=%d\n", addr,
	 (intptr_t) val, (intptr_t) val, sz);
  
  if (intptr_t base_addr = __seahorn_get_abs_base_address(addr)) {
    auto it = abs_to_concr_ptr_map.find(base_addr);
    if (it != abs_to_concr_ptr_map.end()) {
      void *p = it->second;
      intptr_t offset = ((intptr_t) addr - base_addr);
      memcpy((void*)((intptr_t) p + offset), &val, sz);
      sealog("\tinitialized physical address %#lx + %#lx\n", p, offset);
      #if 1
      /// This assumes that sz==sizeof(int)
      int* pp = (int*) ((intptr_t) p + offset);
      sealog("\tContent of %#lx = %d (0x%x)\n",(intptr_t) p + offset, *pp, *pp);
      #endif 
    } else {
      printf("Error: cannot find physical memory for %#lx\n", base_addr);
      exit(1);
    }
  }
}
  
void __seahorn_mem_store (void *src, void *dst, size_t sz) {
  sealog("[sea] __seahorn_mem_store from %p to %p and sz=%d\n", src, dst, sz);

  intptr_t p_src = (intptr_t) src;
  intptr_t p_dst = (intptr_t) dst;
  
  if(intptr_t base_src = __seahorn_get_abs_base_address(src)) {
    sealog("\tFound abstract address for source %p -> %#lx\n", src, base_src);
    auto it = abs_to_concr_ptr_map.find(base_src);
    if (it != abs_to_concr_ptr_map.end()) {
      intptr_t conc_base_src = (intptr_t) it->second;
      intptr_t offset = ((intptr_t) src - base_src);
      p_src = conc_base_src + offset;
      sealog("\tphysical src address %#lx + %#lx = %#lx\n",
	     conc_base_src, offset, p_src);      
	     
    } else {
      printf("Error: cannot find physical memory for %#lx\n", base_src);
      exit(1);
    }
  } else {
    sealog("\tSource is already a physical address.\n");
  }
  
  if(intptr_t base_dst = __seahorn_get_abs_base_address(dst)) {
    sealog("\tFound abstract address for destination %p -> %#lx\n", dst, base_dst);
    auto it = abs_to_concr_ptr_map.find(base_dst);
    if (it != abs_to_concr_ptr_map.end()) {
      intptr_t conc_base_dst = (intptr_t) it->second;
      intptr_t offset = ((intptr_t) dst - base_dst);
      p_dst = conc_base_dst + offset;
      sealog("\tphysical dst address %#lx + %#lx = %#lx\n",
	     conc_base_dst, offset, p_dst);
    } else {
      printf("Error: cannot find physical memory for %#lx\n", base_dst);
      exit(1);
    }
  } else {
    sealog("\tDestination is already a physical address.\n");
  }
  
  memcpy((void*) p_dst, (void*) p_src, sz);
}

void __seahorn_mem_load (void *dst, void *src, size_t sz) {
  sealog("[sea] __seahorn_mem_load from %p to %p and sz=%d\n", src, dst, sz);
  intptr_t p_src = (intptr_t) src;
  intptr_t p_dst = (intptr_t) dst;
  
  if(intptr_t base_src = __seahorn_get_abs_base_address(src)) {
    sealog("\tFound abstract address for source %p -> %#lx\n", src, base_src);
    auto it = abs_to_concr_ptr_map.find(base_src);
    if (it != abs_to_concr_ptr_map.end()) {
      intptr_t conc_base_src = (intptr_t) it->second;
      intptr_t offset = ((intptr_t) src - base_src);
      p_src = conc_base_src + offset;
      sealog("\tphysical src address %#lx + %#lx = %#lx\n",
	     conc_base_src, offset, p_src); 
    } else {
      printf("Error: cannot find physical memory for %#lx\n", base_src);
      exit(1);
    }
  } else {
    sealog("\tSource is already a physical address\n");
  }
  
  if(intptr_t base_dst = __seahorn_get_abs_base_address(dst)) {
    sealog("\tFound abstract address for destination %p -> %#lx\n", dst, base_dst);
    auto it = abs_to_concr_ptr_map.find(base_dst);
    if (it != abs_to_concr_ptr_map.end()) {
      intptr_t conc_base_dst = (intptr_t) it->second;
      intptr_t offset = ((intptr_t) dst - base_dst);
      p_dst = conc_base_dst + offset;
      sealog("\tphysical dst address %#lx + %#lx = %#lx\n",
	     conc_base_dst, offset, p_dst);
    } else {
      printf("Error: cannot find physical memory for %#lx\n", base_dst);
      exit(1);
    }
  } else {
    sealog("\tDestination is already a physical address\n");
  }

  //sealog("source address=%#lx destination address=%#lx\n", p_src, p_dst);
  memcpy((void*) p_dst, (void*) p_src, sz);
  #if 1
  /// This assumes that sz=sizeof(int)
  int* pp_src = (int*) (p_src);
  sealog("\tContent of %#lx = %d (0x%x)\n",p_src, *pp_src, *pp_src);      
  int* pp_dst = (int*) (p_dst);
  sealog("\tContent of %#lx = %d (0x%x)\n",p_dst, *pp_dst, *pp_dst);
  #endif 
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


}
