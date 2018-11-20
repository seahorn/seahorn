// RUN: %sea clp --clp-fapp "%s" -o "%s".clp; OutputCheck --file-to-check="%s".clp "%s"
// CHECK: ^main_verifier_error

// we only check that there is a rule head with signature main_verifier_error

extern int nd(void);
extern void __VERIFIER_error(void) __attribute__((noreturn));
#define assert(X) if(!(X)){__VERIFIER_error();}

int main(){
  int x,y;
  x=1; y=0;
  while (nd ())
    {
      x=x+y;
      y++;
    }
  assert (x>=y);
  return 0;
}

