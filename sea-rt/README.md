To generate and use a counterexample harness follow the following steps

  > sea pf -m64 in.c --cex=cex.ll
  > sea clang -m64 -g -o out.bc in.c cex.ll
  > clang-mp-3.6 -m64 -o out out.bc <INSTALL_ROOT>/lib/libsea-rt.a
  > ./out
  __VERIFIER_error was executed

Option `-m64' is necessary on 64-bit platforms because the run-time
library is compiled under host architecture, but sea-clang defaults to
`-m32'.

The resulting binary can be debugged with gdb, lldb, and valgrind.
