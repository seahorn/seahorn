// RUN: %sea smt --step=flarge --horn-format=mcmt "%s" -o "%s".mcmt; OutputCheck --file-to-check="%s".mcmt "%s"
// CHECK: define-transition-system 

// todo: have a better check

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

