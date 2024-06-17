
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
#define cast_to(x, y) (decltype(x))(y)
#else
#define cast_to(x, y) (typeof(x))(y)
#endif

#ifdef __cplusplus
extern "C" {
#endif

extern char *sea_begin_unique(char *);
extern char *sea_end_unique(char *);
extern char *__sea_set_extptr_slot0_hm(char *ptr, size_t val);
extern size_t __sea_get_extptr_slot0_hm(char *ptr);
extern char *__sea_set_extptr_slot1_hm(char *ptr, size_t val);
extern size_t __sea_get_extptr_slot1_hm(char *ptr);
extern char *sea_set_fatptr_slot(char *ptr, char slot, uint64_t val);
extern uint64_t sea_get_fatptr_slot(char *ptr, char slot);
extern char nd_char(void);
extern uint64_t nd_uint64t(void);
extern char *sea_bor_mkbor(char *);
extern char *sea_bor_mksuc(char *);
extern void sea_die(char *);
extern char *sea_mkown(char *);
extern char *sea_mkshr(char *);
extern char *sea_bor_mem2reg(char *);
extern char *sea_mov_reg2mem(char * /*dst_ptrtoptr*/, char * /*src_ptr*/);
extern bool nd_bool(void);

#ifdef __cplusplus
}
#endif

// Information to bit map
#define HELD_BIT 0x2
#define LENT_BIT 0x1
#define OWN_BIT 0x0

#define GET_BIT(x, loc) (((uint64_t)x & (1 << loc)) >> loc)

#define SET_BIT(x, loc, boolean_value)                                         \
  ((boolean_value) ? ((x) | ((uint64_t)1 << (loc)))                            \
                   : ((x) & ~((uint64_t)1 << (loc))))

#define GET_LENT(x) GET_BIT(x, LENT_BIT)
#define SET_LENT(x, val) SET_BIT(x, LENT_BIT, val)

#define GET_HELD(x) GET_BIT(x, HELD_BIT)
#define SET_HELD(x, val) SET_BIT(x, HELD_BIT, val)

/* FATPTR SLOT MAP
 * slot0 -- carried val
 * slot1 -- returned val at borrowed ptr
 * slot2 -- borrow/ownership checking
 **/
#define CARRY_SLOT 0
#define PROPHECY_SLOT 1
#define OWNERSHIP_SLOT 2

#ifdef OWNSEM_BORCHK
#define borchk_assert(x) sassert(x)
#define borchk_assume(x) assume(x)
#else
#define borchk_assert(x) ;
#define borchk_assume(x) ;
#endif

#define SEA_SET_FATPTR_SLOT0(SRC, VAL)                                         \
  do {                                                                         \
    (SRC) =                                                                    \
        cast_to(SRC, sea_set_fatptr_slot((char *)(SRC), 0, (uint64_t)VAL));    \
  } while (0);

#define SEA_SET_FATPTR_SLOT1(SRC, VAL)                                         \
  do {                                                                         \
    (SRC) =                                                                    \
        cast_to(SRC, sea_set_fatptr_slot((char *)(SRC), 1, (uint64_t)VAL));    \
  } while (0);

#define SEA_SET_FATPTR_SLOT2(SRC, VAL)                                         \
  do {                                                                         \
    (SRC) =                                                                    \
        cast_to(SRC, sea_set_fatptr_slot((char *)(SRC), 2, (uint64_t)VAL));    \
  } while (0);

#define SEA_SET_FATPTR_SLOT(SRC, SLOT, VAL)                                    \
  do {                                                                         \
    (SRC) =                                                                    \
        cast_to(SRC, sea_set_fatptr_slot((char *)SRC, SLOT, (uint64_t)VAL));   \
  } while (0);

#define SEA_GET_FATPTR_SLOT0(SRC, VAL)                                         \
  do {                                                                         \
    (VAL) = cast_to(VAL, sea_get_fatptr_slot((char *)SRC, 0));                 \
  } while (0);

#define SEA_GET_FATPTR_SLOT1(SRC, VAL)                                         \
  do {                                                                         \
    (VAL) = cast_to(VAL, sea_get_fatptr_slot((char *)SRC, 1));                 \
  } while (0);

#define SEA_GET_FATPTR_SLOT2(SRC, VAL)                                         \
  do {                                                                         \
    (VAL) = cast_to(VAL, sea_get_fatptr_slot((char *)(SRC), 2));               \
  } while (0);

#define SEA_GET_FATPTR_SLOT(SRC, SLOT, VAL)                                    \
  do {                                                                         \
    (VAL) = cast_to(VAL, sea_get_fatptr_slot((char *)SRC, SLOT));              \
  } while (0);

#define SEA_GET_LENT(SRC, VAL)                                                 \
  do {                                                                         \
    uint64_t intmd;                                                            \
    SEA_GET_FATPTR_SLOT2((char *)(SRC), intmd);                                \
    (VAL) = GET_LENT(intmd);                                                   \
  } while (0);

#define SEA_SET_LENT(SRC, VAL)                                                 \
  do {                                                                         \
    uint64_t intmd;                                                            \
    SEA_GET_FATPTR_SLOT2((SRC), intmd);                                        \
    uint64_t new_intmd = SET_LENT(intmd, (bool)VAL);                           \
    SEA_SET_FATPTR_SLOT2((SRC), new_intmd);                                    \
  } while (0);

#define SEA_GET_HELD(SRC, VAL)                                                 \
  do {                                                                         \
    uint64_t intmd;                                                            \
    SEA_GET_FATPTR_SLOT2((SRC), intmd);                                        \
    (VAL) = GET_HELD(intmd);                                                   \
  } while (0);

#define SEA_SET_HELD(SRC, VAL)                                                 \
  do {                                                                         \
    uint64_t intmd;                                                            \
    SEA_GET_FATPTR_SLOT2((SRC), intmd);                                        \
    uint64_t new_intmd = SET_HELD(intmd, (bool)VAL);                           \
    SEA_SET_FATPTR_SLOT2((char *)(SRC), (uint64_t)new_intmd);                  \
  } while (0);

#define ENTANGLE_BIT(SRC, SRC_SLOT, SRC_SLOT_BIT, DST, DST_SLOT, DST_SLOT_BIT, \
                     PROPHECY_VAR)                                             \
  do {                                                                         \
    uint64_t intmd_src;                                                        \
    SEA_GET_FATPTR_SLOT(SRC, SRC_SLOT, intmd_src);                             \
    uint64_t intmd_dst;                                                        \
    SEA_GET_FATPTR_SLOT(DST, DST_SLOT, intmd_dst);                             \
    uint64_t new_intmd_src = SET_BIT(intmd_src, SRC_SLOT_BIT, PROPHECY_VAR);   \
    uint64_t new_intmd_dst = SET_BIT(intmd_dst, DST_SLOT_BIT, PROPHECY_VAR);   \
    SEA_SET_FATPTR_SLOT(SRC, SRC_SLOT, new_intmd_src);                         \
    SEA_SET_FATPTR_SLOT(DST, DST_SLOT, new_intmd_dst);                         \
  } while (0);

// NOTE: intrinsic
#define SEA_MKOWN(SRC)                                                         \
  do {                                                                         \
    uint64_t nd_slot0 = nd_uint64t();                                          \
    uint64_t nd_slot1 = nd_uint64t();                                          \
    char *intmd0, *intmd1, *intmd2;                                            \
    intmd0 = sea_mkown((char *)(SRC));                                         \
    SEA_SET_FATPTR_SLOT0(intmd0, nd_slot0);                                    \
    SEA_SET_FATPTR_SLOT1(intmd0, nd_slot1);                                    \
    (SRC) = (typeof(SRC))intmd0;                                               \
    /* Set lent field to false  */                                             \
    SEA_SET_LENT(SRC, false);                                                  \
  } while (0)

#define SEA_MKOWN_FAST(SRC)                                                    \
  do {                                                                         \
    uint64_t nd_slot0 = nd_uint64t();                                          \
    uint64_t nd_slot1 = nd_uint64t();                                          \
    char *intmd0, *intmd1, *intmd2;                                            \
    intmd0 = sea_mkown((char *)(SRC));                                         \
    SEA_SET_FATPTR_SLOT0(intmd0, nd_slot0);                                    \
    SEA_SET_FATPTR_SLOT1(intmd0, nd_slot1);                                    \
    (SRC) = (typeof(SRC))intmd0;                                               \
  } while (0)

#define SEA_FK_MKOWN(SRC)                                                      \
  do {                                                                         \
    SRC = (typeof(SRC))sea_mkown((char *)(SRC));                               \
  } while (0)

// NOTE: intrinsic
#define SEA_MKSHR(SRC)                                                         \
  do {                                                                         \
    (SRC) = (typeof(SRC))sea_mkshr((char *)(SRC));                             \
  } while (0)

// NOTE: intrinsic
#define SEA_BEGIN_UNIQUE(SRC)                                                  \
  do {                                                                         \
    (SRC) = (typeof(SRC))sea_begin_unique((char *)(SRC));                      \
  } while (0)

// NOTE: intrinsic
#define SEA_END_UNIQUE(SRC)                                                    \
  do {                                                                         \
    (SRC) = (typeof(SRC))sea_end_unique((char *)(SRC));                        \
  } while (0)

// NOTE: intrinsic
#define SEA_BEGIN_UNIQUE_AND_LOAD_CACHE(SRC, VAL)                              \
  do {                                                                         \
    (SRC) = (typeof(SRC))sea_begin_unique((char *)SRC);                        \
    SEA_SET_FATPTR_SLOT0((SRC), VAL);                                          \
  } while (0)

// TODO: make cache nd after unloading
// NOTE: intrinsic
#define SEA_UNLOAD_CACHE_AND_END_UNIQUE(SRC, DSTADDRESS, DSTLEN)               \
  do {                                                                         \
    char uniqval = __sea_get_extptr_slot0_hm((char *)SRC);                     \
    (SRC) = (typeof(SRC))sea_end_unique((char *)(SRC));                        \
    memset((char *)DSTADDRESS, uniqval, 1 /* FIXME: use DSTLEN */);            \
  } while (0)

// NOTE: intrinsic
#define SEA_WRITE_CACHE(SRC, VAL)                                              \
  do {                                                                         \
    SEA_SET_FATPTR_SLOT0(SRC, (VAL));                                          \
  } while (0)

// NOTE: intrinsic
#define SEA_READ_CACHE(VAL, SRC)                                               \
  do {                                                                         \
    SEA_GET_FATPTR_SLOT0((char *)SRC, VAL);                                    \
  } while (0)

// NOTE: intrinsic
#define SEA_FK_BORROW(BOR, SRC)                                                \
  do {                                                                         \
    (BOR) = cast_to(BOR, sea_bor_mkbor((char *)SRC));                          \
    (SRC) = cast_to(SRC, sea_bor_mksuc((char *)SRC));                          \
  } while (0);

#ifdef OWNSEM_BORCHK
#define SEA_BORROW(BOR, SRC) SEA_BORROW_CHK(BOR, SRC)
#else
#define SEA_BORROW(BOR, SRC) SEA_BORROW_CHK(BOR, SRC)
#endif

#define SEA_BORROW_FAST(BOR, SRC)                                              \
  do {                                                                         \
    (BOR) = cast_to(BOR, sea_bor_mkbor((char *)SRC));                          \
    (SRC) = cast_to(SRC, sea_bor_mksuc((char *)SRC));                          \
    uint64_t brval;                                                            \
    SEA_GET_FATPTR_SLOT0((SRC), brval);                                        \
    SEA_SET_FATPTR_SLOT0((BOR), brval);                                        \
    uint64_t ndval = nd_uint64t();                                             \
    SEA_SET_FATPTR_SLOT1((BOR), ndval)                                         \
    SEA_SET_FATPTR_SLOT0((SRC), ndval);                                        \
  } while (0);

#define SEA_BORROW_CHK(BOR, SRC)                                               \
  do {                                                                         \
    uint64_t src_own_data;                                                     \
    SEA_GET_FATPTR_SLOT(SRC, OWNERSHIP_SLOT, src_own_data);                    \
    bool is_lent = GET_LENT(src_own_data);                                     \
    borchk_assert(!is_lent);                                                   \
    (BOR) = cast_to(BOR, sea_bor_mkbor((char *)SRC));                          \
    (SRC) = cast_to(SRC, sea_bor_mksuc((char *)SRC));                          \
    uint64_t brval;                                                            \
    SEA_GET_FATPTR_SLOT0((SRC), brval);                                        \
    SEA_SET_FATPTR_SLOT0((BOR), brval);                                        \
    uint64_t ndval = nd_uint64t();                                             \
    SEA_SET_FATPTR_SLOT1((BOR), ndval)                                         \
    SEA_SET_FATPTR_SLOT0((SRC), ndval);                                        \
    /*borrow logic: choose action: */                                          \
    /*borrow logic: SRC gives new loan or SRC transfers held loan  */          \
    bool create_loan = nd_bool();                                              \
    if (create_loan) {                                                         \
      /* 1. create new loan  */                                                \
      bool fresh_loan = nd_bool();                                             \
      /* 2. entangle src lent bit and dst held bit */                          \
      ENTANGLE_BIT(SRC, OWNERSHIP_SLOT, LENT_BIT, BOR, OWNERSHIP_SLOT,         \
                   HELD_BIT, fresh_loan);                                      \
    } else {                                                                   \
      /*Transfer: Held loan already copied to BOR; */                          \
      /*just set SRC held loan to false */                                     \
      uint64_t own_data;                                                       \
      SEA_GET_FATPTR_SLOT(SRC, OWNERSHIP_SLOT, own_data);                      \
      uint64_t new_own_data = SET_HELD(own_data, false);                       \
      SEA_SET_FATPTR_SLOT(SRC, OWNERSHIP_SLOT, new_own_data);                  \
    }                                                                          \
    /* Borrow lent bit should be false */                                      \
    uint64_t bor_data;                                                         \
    SEA_GET_FATPTR_SLOT(BOR, OWNERSHIP_SLOT, bor_data);                        \
    uint64_t new_bor_data = SET_LENT(bor_data, false);                         \
    SEA_SET_FATPTR_SLOT(BOR, OWNERSHIP_SLOT, new_bor_data);                    \
  } while (0);

#define SEA_MOVE2MEM(PTR_TO_SRC_PTR, SRC)                                      \
  do {                                                                         \
    (SRC) = (typeof(SRC))sea_mov_reg2mem((char *)SRC, (char *)PTR_TO_SRC_PTR); \
    *(PTR_TO_SRC_PTR) = (typeof(SRC))(SRC);                                    \
  } while (0);

#ifdef OWNSEM_BORCHK
#define SEA_DIE(SRC) SEA_DIE_CHK(SRC)
#else
#define SEA_DIE(SRC) SEA_DIE_FAST(SRC)
#endif

// NOTE: intrinsic
#define SEA_DIE_FAST(SRC)                                                      \
  do {                                                                         \
    uint64_t nd_retval;                                                        \
    SEA_GET_FATPTR_SLOT1((char *)(SRC), nd_retval);                            \
    uint64_t cacheval;                                                         \
    SEA_GET_FATPTR_SLOT0((char *)(SRC), cacheval);                             \
    assume(nd_retval == cacheval);                                             \
    sea_die((char *)(SRC));                                                    \
  } while (0);

// NOTE: intrinsic
#define SEA_DIE_CHK(SRC)                                                       \
  do {                                                                         \
    uint64_t nd_retval;                                                        \
    SEA_GET_FATPTR_SLOT1((char *)(SRC), nd_retval);                            \
    uint64_t cacheval;                                                         \
    SEA_GET_FATPTR_SLOT0((char *)(SRC), cacheval);                             \
    assume(nd_retval == cacheval);                                             \
    bool lent;                                                                 \
    SEA_GET_LENT((char *)SRC, lent);                                           \
    borchk_assert(lent == false);                                              \
    bool held;                                                                 \
    SEA_GET_HELD((char *)SRC, held);                                           \
    borchk_assume(held == false);                                              \
    sea_die((char *)(SRC));                                                    \
  } while (0)

// NOTE: intrinsic
#define SEA_LOAD_CACHE_AND_BORROW(BOR, SRC, VAL)                               \
  do {                                                                         \
    char *intmd = __sea_set_extptr_slot0_hm((char *)(SRC), (VAL));             \
    SEA_BORROW((BOR), intmd);                                                  \
  } while (0)

// NOTE: intrinsic
#define SEA_BORROW_OFFSET(BOR_OFF, SRC, OFFSET)                                \
  do {                                                                         \
    char *boroff_intmd0;                                                       \
    SEA_BORROW(boroff_intmd0, SRC);                                            \
    (BOR_OFF) = ((typeof(BOR_OFF))(boroff_intmd0)) + OFFSET;                   \
  } while (0)

// NOTE: intrinsic
#define SEA_BORROW_LOAD(BOR, PTR_TO_SRC_PTR)                                   \
  do {                                                                         \
    char *intmd_ptrptrto = sea_bor_mem2reg((char *)(PTR_TO_SRC_PTR));          \
    typeof(BOR)(mem2reg_ptr) = *((typeof(PTR_TO_SRC_PTR))intmd_ptrptrto);      \
    SEA_BORROW(BOR, mem2reg_ptr);                                              \
    *(PTR_TO_SRC_PTR) = mem2reg_ptr;                                           \
  } while (0)
