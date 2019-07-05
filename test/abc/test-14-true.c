// RUN: %sea abc -O0 --encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

struct foo {
  int x;
  int y;
};

struct foo gv_;
struct foo *gv = &gv_;

int main() {
  gv->y = 10; // (*gv).y = 10;
  return 0;
}
