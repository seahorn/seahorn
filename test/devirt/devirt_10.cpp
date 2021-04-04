// RUN: %sea fpf -O3 --inline --no-lower-gv-init-struct --horn-unify-assumes=true --horn-gsa --no-fat-fns=bcmp,memcpy,assert_bytes_match,ensure_linked_list_is_allocated,sea_aws_linked_list_is_valid --dsa=sea-cs-t --devirt-functions=sea-dsa --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=true --horn-bmc-coi=true --sea-opsem-allocator=static --horn-explicit-sp0=false --horn-bv2-lambdas --horn-bv2-simplify=true --horn-bv2-extra-widemem "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"
class BaseClass {
public:
  BaseClass() {}
  virtual ~BaseClass() {}
  virtual int Func() { return 0; }
};
class DerivedClass : public BaseClass {
public:
  DerivedClass() {}
  int Func() { return 1; }
};
int main(int argc, char **argv) {
  BaseClass *bc = new DerivedClass();

  // Devirtualization should lower the virtual call to either a call
  // to BaseClass::Func or DerivedClass::Func. 
  
  sassert(bc->Func() == 1);
  return 0;
}
