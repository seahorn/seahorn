// sea_printf in the sea-mlir export: one strong sea.print per integer or
// pointer argument, labelled by the format's text before the conversion
// (else the variable's name, else arg<k>), with the conversion's format;
// a call without arguments is a tag line; a double is not printed, and a
// format that does not match the arguments gives positional / variable
// labels and sea-mlir's auto format (warnings). The prints encode nothing
// in the VC.
// RUN: %sea yama -y sea-mlir-export --bound=1 -m64 -g --horn-sea-mlir-out=%t.mlir "%s" 2>&1 | filecheck %s --check-prefix=LOG
// RUN: filecheck %s < %t.mlir
// LOG: sea_printf at line {{[0-9]+}}: argument 1 (d) of type double is not printed
// LOG: sea_printf at line {{[0-9]+}}: cannot match the format "two %d %d\0A" to its 1 arguments
// LOG: sea-mlir-export: wrote
// CHECK: sea.print "x" %[[X:v[0-9]+]] : i32 {fmt = "s"}
// CHECK-NEXT: sea.print "u" %[[U:v[0-9]+]] : i32 {fmt = "u"}
// CHECK: sea.print "p" %{{v[0-9]+}} : !sea.ptr<64>
// CHECK-NEXT: sea.print "hex" %[[U]] : i32 {fmt = "x"}
// CHECK-NEXT: sea.print "c" %[[X]] : i32 {fmt = "c"}
// CHECK-NEXT: sea.print "name = \"literal\""
// CHECK-NEXT: sea.print "plain tag"
// CHECK-NEXT: sea.print "sum" %{{v[0-9]+}} : i32 {fmt = "s"}
// CHECK: sea.print "x" %[[X]] : i32 loc(
// CHECK-NEXT: sea.print "line1 line2"
// CHECK-NOT: sea.print

extern int nd_int(void);
extern unsigned nd_uint(void);
extern void __VERIFIER_error(void);
extern __declspec(noalias) void sea_printf(const char *format, ...);
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

int main(void) {
  int x = nd_int();
  unsigned u = nd_uint();
  char buf[8];
  char *p = buf + (u & 3);
  int sum = x + (int)u;
  sea_printf("x=%d u=%u\n", x, u);
  sea_printf("p: %p, hex %x, c %c, name %s", p, u, x, "literal");
  sea_printf("plain tag\n");
  sea_printf("%d\n", sum);
  sea_printf("d=%f", (double)x);
  sea_printf("two %d %d\n", x);
  sea_printf("line1\nline2\n");
  sassert(x != 5 || u != 7);
  return 0;
}
