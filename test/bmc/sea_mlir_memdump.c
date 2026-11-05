// sea_memdump(label, p, n) (seahorn.h) in the sea-mlir export: a strong
// sea.print.mem hex dump of the n bytes at p, in the memory version current
// at the call (the shadow memory passes it as shadow.mem.arg.ref; the call
// defines no memory); a label that is not a constant string prints as
// "sea_memdump" (a warning). The prints encode nothing in the VC.
// RUN: %sea yama -y sea-mlir-export --bound=9 -m64 -g --horn-sea-mlir-out=%t.mlir "%s" 2>&1 | filecheck %s --check-prefix=LOG
// RUN: filecheck %s < %t.mlir
// LOG: sea_memdump at line {{[0-9]+}}: the label is not a constant string
// LOG: sea-mlir-export: wrote
// CHECK: sea.print.mem "buf" %[[M:v[0-9]+]][%{{v[0-9]+}}], %{{v[0-9]+}} : !sea.mem<!sea.ptr<64>, i8>, i64 -> i8 {fmt = "hexdump"}
// CHECK: sea.print.mem "s" %{{v[0-9]+}}[%{{v[0-9]+}}], %{{v[0-9]+}} : !sea.mem<!sea.ptr<64>, i8>, i64 -> i8 {fmt = "hexdump"}
// CHECK: sea.print.mem "sea_memdump" %{{v[0-9]+}}[%{{v[0-9]+}}], %{{v[0-9]+}} : !sea.mem<!sea.ptr<64>, i8>, i64 -> i8 {fmt = "hexdump"}
// CHECK-NOT: sea.print.mem

#include <seahorn/seahorn.h>
#include <stdint.h>

extern int nd_int(void);
struct S {
  uint32_t a;
  uint8_t b[6];
  uint16_t c;
};

int main(void) {
  uint8_t buf[8];
  struct S s;
  for (int i = 0; i < 8; i++)
    buf[i] = (uint8_t)(nd_int() & 0x3f) + 'A';
  s.a = nd_int();
  s.b[0] = buf[0];
  s.c = 7;
  sea_memdump("buf", buf, sizeof buf);
  sea_memdump("s", &s, sizeof s);
  sea_memdump(nd_int() ? "x" : "y", buf, (size_t)(nd_int() & 7));
  sassert(buf[3] != 'Q' || s.a != 5);
  return 0;
}
