extern int __VERIFIER_NONDET();
extern void __VERIFIER_error() __attribute__((noreturn));

/*

This command is enough to prove program is safe:

  sea pf test-1.c --crab 

This achived because LLVM lower global variables to registers and due
to the invariants provided by crab.

If we turn off llvm optimizations the above command cannot prove
safety anymore. But we can still prove safety by running the following
command:

sea pf -O0 test-1.c --crab --crab-print-invariants --crab-track=arr \
                    --crab-singleton-aliases --horn-singleton-aliases 

--crab-track=arr : crab infers invariants about memory contents
                   (global variables are translated to pointers by
                   llvm)

--crab-singleton-aliases: allow crab to pass invariants about global
                          variables to SeaHorn.

--horn-singleton-aliases: SeaHorn translates global variables as
                          scalars if it is safe to do so.
*/

int x = 1;
int y = 0;


int main (){
  while (__VERIFIER_NONDET())
  {
    x=x+y;
    y++;
  }

  if (!(x>=y)) __VERIFIER_error ();

  return 42;
}

