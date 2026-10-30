# fat_ptr_symbolic (stale)

These tests cover the fat-pointer-as-intrinsics approach: the
`FatBufferBoundsCheck` instrumentation (`seapp -fat-bnd-check`) and the
`__sea_*_extptr_*` intrinsics, interpreted symbolically by `BvOpSem2`.

That approach was superseded by the wide memory models
(`--horn-bv2-widemem`, `--horn-bv2-extra-widemem`), which build wide
pointers into the memory model. The tests still pass, so they stay until
the instrumentation, the intrinsics and their `sea-rt` runtime are
removed; delete this directory together with that code.
