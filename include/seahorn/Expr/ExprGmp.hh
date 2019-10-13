/// A simple interface to gmp
#pragma once
#include <algorithm>
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
  mpz_class() { mpz_init(m_num); }
  ~mpz_class() { mpz_clear(m_num); }

  mpz_class(const mpz_class &v) { mpz_init_set(m_num, v.m_num); }
  mpz_class(mpz_class &&v) {
    *m_num = *v.m_num;
    mpz_init(v.m_num);
  }

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
};
} // namespace expr
