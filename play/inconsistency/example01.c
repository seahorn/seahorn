extern int nd ();

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
__attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }

#define assume __VERIFIER_assume

int example1() {
    int k=0;
    int x = nd ();
    assume (x>0);
    for (int i=-x; i<x; i++) {
        assert(i!=0);
        k=1/1;
    }
    return k;
}
