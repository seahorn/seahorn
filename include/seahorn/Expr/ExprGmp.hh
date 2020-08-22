/// A simple interface to gmp
#pragma once
#include <algorithm>
#include <cassert>
#include <cstring>
#include <gmp.h>
#include <string>

namespace expr {

namespace {
extern "C" {
typedef void (*__gmp_freefunc_t)(void *, size_t);
}
struct scoped_cstring {
  char *m_str;
  scoped_cstring(char *s) { m_str = s; }
  ~scoped_cstring() {
    __gmp_freefunc_t freefunc;
    mp_get_memory_functions(nullptr, nullptr, &freefunc);
    (*freefunc)(m_str, std::strlen(m_str) + 1);
  }
};
} // namespace
class mpz_class {
  mpz_t m_num;

public:
  friend class mpz_rand;

  mpz_class() { mpz_init(m_num); }
  ~mpz_class() { mpz_clear(m_num); }

  mpz_class(const mpz_class &v) { mpz_init_set(m_num, v.m_num); }
  mpz_class(mpz_class &&v) {
    *m_num = *v.m_num;
    mpz_init(v.m_num);
  }

  mpz_class(mpz_srcptr v) { mpz_init_set(m_num, v); }
  mpz_class(int v) { mpz_init_set_si(m_num, v); }
  mpz_class(unsigned v) { mpz_init_set_ui(m_num, v); }
  mpz_class(unsigned long v) { mpz_init_set_ui(m_num, v); }
  mpz_class(signed long v) { mpz_init_set_si(m_num, v); }

  mpz_class(const std::string &v, int base = 10) {
    if (mpz_init_set_str(m_num, v.c_str(), base) != 0) {
      assert(0);
      std::exit(1);
    }
  }

  int sgn() const { return mpz_sgn(m_num); }

  mpz_class &operator=(const mpz_class &v) {
    mpz_set(m_num, v.m_num);
    return *this;
  }
  mpz_class &operator=(mpz_class &&v) {
    swap(v);
    return *this;
  }

  mpz_class &neg() {
    mpz_neg(m_num, m_num);
    return *this;
  }

  void swap(mpz_class &v) { std::swap(*m_num, *v.m_num); }

  mpz_srcptr get_mpz_t() const { return m_num; }
  mpz_ptr get_mpz_t() { return m_num; }

  signed long int get_si() const { return mpz_get_si(m_num); }
  unsigned long int get_ui() const { return mpz_get_ui(m_num); }
  std::string to_string(unsigned base = 10) const {
    scoped_cstring res(mpz_get_str(0, base, m_num));
    return std::string(res.m_str);
  }

  void mpzExport(void *rop, size_t *count, int order, size_t size, int endian,
                 size_t nails) {
    mpz_export(rop, count, order, size, endian, nails, m_num);
  }

  size_t sizeInBase(int base) const { return mpz_sizeinbase(m_num, base); }

  bool operator<(unsigned long v) const { return mpz_cmp_ui(m_num, v) < 0; }
  bool operator<(signed long v) const { return mpz_cmp_si(m_num, v) < 0; }
  bool operator>(unsigned long v) const { return mpz_cmp_ui(m_num, v) > 0; }
  bool operator>(signed long v) const { return mpz_cmp_si(m_num, v) > 0; }
  bool operator<=(unsigned long v) const { return mpz_cmp_ui(m_num, v) <= 0; }
  bool operator<=(signed long v) const { return mpz_cmp_si(m_num, v) <= 0; }
  bool operator>=(unsigned long v) const { return mpz_cmp_ui(m_num, v) >= 0; }
  bool operator>=(signed long v) const { return mpz_cmp_si(m_num, v) >= 0; }

  bool operator<(const mpz_class &v) const {
    return mpz_cmp(m_num, v.m_num) < 0;
  }
  bool operator>(const mpz_class &v) const {
    return mpz_cmp(m_num, v.m_num) > 0;
  }
  bool operator<=(const mpz_class &v) const {
    return mpz_cmp(m_num, v.m_num) <= 0;
  }
  bool operator>=(const mpz_class &v) const {
    return mpz_cmp(m_num, v.m_num) >= 0;
  }
  bool operator==(const mpz_class &v) const {
    return mpz_cmp(m_num, v.m_num) == 0;
  }
  bool operator!=(const mpz_class &v) const {
    return mpz_cmp(m_num, v.m_num) != 0;
  }

  explicit operator bool() const { return (*this) != 0; }

  mpz_class operator%(const mpz_class &v) {
    mpz_class mod;
    mpz_mod(mod.m_num, m_num, v.m_num);

    return mod;
  }

  mpz_class operator%(unsigned v) {
    mpz_class mod;
    mpz_mod_ui(mod.m_num, m_num, v);

    return mod;
  }

  mpz_class operator+(const mpz_class &v) {
    mpz_class sum;
    mpz_add(sum.m_num, m_num, v.m_num);

    return sum;
  }

  mpz_class operator-(const mpz_class &v) const {
    mpz_class diff;
    mpz_sub(diff.m_num, m_num, v.m_num);

    return diff;
  }

  mpz_class operator*(const mpz_class &v) const {
    mpz_class prod;
    mpz_mul(prod.m_num, m_num, v.m_num);

    return prod;
  }

  mpz_class operator&(const mpz_class &v) const {
    mpz_class result;
    mpz_and(result.m_num, m_num, v.m_num);

    return result;
  }

  mpz_class operator|(const mpz_class &v) const {
    mpz_class result;
    mpz_ior(result.m_num, m_num, v.m_num);

    return result;
  }

  mpz_class operator^(const mpz_class &v) const {
    mpz_class result;
    mpz_xor(result.m_num, m_num, v.m_num);

    return result;
  }

  mpz_class operator~() const {
    mpz_class result;
    mpz_com(result.m_num, m_num);

    return result;
  }

  mpz_class operator<<(mp_bitcnt_t v) const {
    mpz_class result;
    mpz_mul_2exp(result.m_num, m_num, v);

    return result;
  }

  mpz_class operator>>(mp_bitcnt_t v) const {
    mpz_class result;
    mpz_tdiv_q_2exp(result.m_num, m_num, v);

    return result;
  }
};

class mpz_rand {
  gmp_randstate_t m_state;

public:
  mpz_rand(mpz_class seed) {
    gmp_randinit_default(m_state);
    gmp_randseed(m_state, seed.m_num);
  }

  mpz_class urandomb(mp_bitcnt_t n) {
    mpz_class mpz;
    mpz_urandomb(mpz.m_num, m_state, n);
    return mpz;
  }
};
class mpq_class {
  mpq_t m_num;

public:
  mpq_class() { mpq_init(m_num); }
  ~mpq_class() { mpq_clear(m_num); }

  mpq_class(const mpq_class &v) {
    mpz_init_set(mpq_numref(m_num), mpq_numref(v.m_num));
    mpz_init_set(mpq_denref(m_num), mpq_denref(v.m_num));
  }
  mpq_class(mpq_class &&v) {
    *m_num = *v.m_num;
    mpq_init(v.m_num);
  }

  mpq_class(mpq_srcptr v) {
    mpz_init_set(mpq_numref(m_num), mpq_numref(v));
    mpz_init_set(mpq_denref(m_num), mpq_denref(v));
  }
  mpq_class(int v) {
    mpq_init(m_num);
    mpq_set_si(m_num, v, 1);
  }
  mpq_class(unsigned v) {
    mpq_init(m_num);
    mpq_set_ui(m_num, v, 1);
  }
  mpq_class(signed long v) {
    mpq_init(m_num);
    mpq_set_si(m_num, v, 1);
  }
  mpq_class(unsigned long v) {
    mpq_init(m_num);
    mpq_set_ui(m_num, v, 1);
  }

  mpq_class(const std::string &v, int base = 10) {
    mpq_init(m_num);
    if (mpq_set_str(m_num, v.c_str(), base) != 0) {
      assert(0);
      mpq_clear(m_num);
      std::exit(1);
    }
  }

  void canonicalize() { mpq_canonicalize(m_num); }
  int sgn() const { return mpq_sgn(m_num); }

  mpq_class &operator=(const mpq_class &v) {
    mpq_set(m_num, v.m_num);
    return *this;
  }
  mpq_class &operator=(mpq_class &&v) {
    swap(v);
    return *this;
  }

  mpq_class &neg() {
    mpq_neg(m_num, m_num);
    return *this;
  }

  void swap(mpq_class &v) { std::swap(*m_num, *v.m_num); }

  mpq_srcptr get_mpq_t() const { return m_num; }
  mpq_ptr get_mpq_t() { return m_num; }

  std::string to_string(unsigned base = 10) const {
    scoped_cstring res(mpq_get_str(0, base, m_num));
    return std::string(res.m_str);
  }

  bool operator<(const mpq_class &v) const {
    return mpq_cmp(m_num, v.m_num) < 0;
  }
  bool operator>(const mpq_class &v) const {
    return mpq_cmp(m_num, v.m_num) > 0;
  }
  bool operator<=(const mpq_class &v) const {
    return mpq_cmp(m_num, v.m_num) <= 0;
  }
  bool operator>=(const mpq_class &v) const {
    return mpq_cmp(m_num, v.m_num) >= 0;
  }
  bool operator==(const mpq_class &v) const {
    return mpq_equal(m_num, v.m_num);
  }
};
} // namespace expr
