#pragma once

#include "seahorn/Expr/Expr.hh"

#include <boost/functional/hash.hpp>

#include "llvm/ADT/APInt.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"

#include <boost/lexical_cast.hpp>

namespace expr {
using namespace llvm;

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, const Expr &p) {
  OS << p.get();
  return OS;
}

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, const ENode &n) {
  OS << boost::lexical_cast<std::string>(n);
  return OS;
}

using namespace llvm;
template <> struct TerminalTrait<const Function *> {
  static inline void print(std::ostream &OS, const Function *f, int depth,
                           bool brkt) {
    OS << f->getName().str();
  }

  static inline bool less(const Function *f1, const Function *f2) {
    return f1 < f2;
  }

  static inline bool equal_to(const Function *f1, const Function *f2) {
    return f1 == f2;
  }

  static inline size_t hash(const Function *f) {
    boost::hash<const Function *> hasher;
    return hasher(f);
  }

  static TerminalKind getKind() {return TerminalKind::LLVM_FUNCTION;}
  static std::string name() {return "llvm::Function";}
};

template <> struct TerminalTrait<const BasicBlock *> {
  static inline void print(std::ostream &OS, const BasicBlock *s, int depth,
                           bool brkt) {
    OS << s->getParent()->getName().str() + "@" + s->getName().str();
  }
  static inline bool less(const BasicBlock *s1, const BasicBlock *s2) {
    return s1 < s2;
  }

  static inline bool equal_to(const BasicBlock *b1, const BasicBlock *b2) {
    return b1 == b2;
  }

  static inline size_t hash(const BasicBlock *b) {
    boost::hash<const BasicBlock *> hasher;
    return hasher(b);
  }

  static TerminalKind getKind() {return TerminalKind::LLVM_BASICBLOCK;}
  static std::string name() {return "llvm::BasicBlock";}
};


template <> struct TerminalTrait<const Value *> {
  static inline void print(std::ostream &OS, const Value *s, int depth,
                           bool brkt) {
    // -- name instructions uniquely based on the name of their containing
    // function
    if (const Instruction *inst = dyn_cast<const Instruction>(s)) {
      const BasicBlock *bb = inst->getParent();
      const Function *fn = bb ? bb->getParent() : NULL;
      if (fn)
        OS << fn->getName().str() << "@";
    } else if (const Argument *arg = dyn_cast<const Argument>(s)) {
      const Function *fn = arg->getParent();
      if (fn)
        OS << fn->getName().str() << "@";
    }

    if (s->hasName()) {
      OS << (isa<GlobalValue>(s) ? '@' : '%') << s->getName().str();
    } else if (const Argument *arg = dyn_cast<const Argument>(s)) {
      OS << "arg." << arg->getArgNo();
    } else {
      // names of constant expressions
      std::string ssstr;
      raw_string_ostream ss(ssstr);
      ss << *s;
      OS << ss.str();

      // std::string str = ss.str();
      // int f = str.find_first_not_of(' ');
      // std::string s1 = str.substr(f);
      // f = s1.find_first_of(' ');
      // OS << s1.substr(0,f);
    }
  }
  static inline bool less(const Value *s1, const Value *s2) { return s1 < s2; }

  static inline bool equal_to(const Value *v1, const Value *v2) {
    return v1 == v2;
  }

  static inline size_t hash(const Value *v) {
    boost::hash<const Value *> hasher;
    return hasher(v);
  }

  static TerminalKind getKind() {return TerminalKind::LLVM_VALUE;}
  static std::string name() {return "llvm::Value";}
};

using BB = expr::Terminal<const llvm::BasicBlock *>;
using VALUE = expr::Terminal<const llvm::Value *>;
using FUNCTION = expr::Terminal<const llvm::Function *>;

/** Converts v to ::mpz_class. Assumes that v is signed */
inline expr::mpz_class toMpz(const llvm::APInt &v) {
  // Based on:
  // https://llvm.org/svn/llvm-project/polly/trunk/lib/Support/GICHelper.cpp
  // return v.getSExtValue ();

  llvm::APInt abs;
  abs = v.isNegative() ? v.abs() : v;

  const uint64_t *rawdata = abs.getRawData();
  unsigned numWords = abs.getNumWords();

  // TODO: Check if this is true for all platforms.
  expr::mpz_class res;
  mpz_import(res.get_mpz_t(), numWords, -1, sizeof(uint64_t), 0, 0, rawdata);

  if (v.isNegative())
    res.neg();
  return res;
}

inline expr::mpz_class toMpz(const Value *v) {
  if (const ConstantInt *k = dyn_cast<ConstantInt>(v))
    return toMpz(k->getValue());
  if (isa<ConstantPointerNull>(v))
    return mpz_class();

  assert(0 && "Not a number");
  return mpz_class();
}

/** Adapted from
    https://llvm.org/svn/llvm-project/polly/branches/release_34/lib/Support/GICHelper.cpp
*/
inline APInt toAPInt(const expr::mpz_class &v) {
  uint64_t *p = nullptr;
  size_t sz;

  p = (uint64_t *)mpz_export(p, &sz, -1, sizeof(uint64_t), 0, 0, v.get_mpz_t());
  if (p) {
    APInt A((unsigned)mpz_sizeinbase(v.get_mpz_t(), 2), (unsigned)sz, p);
    A = A.zext(A.getBitWidth() + 1);
    free(p);

    if (v.sgn() == -1)
      return -A;
    else
      return A;
  } else
    return APInt(1, 0);
}

inline APInt toAPInt(unsigned numBits, const expr::mpz_class &v) {
  uint64_t *p = nullptr;
  size_t sz;

  p = (uint64_t *)mpz_export(p, &sz, -1, sizeof(uint64_t), 0, 0, v.get_mpz_t());
  if (p) {
    APInt A(numBits, (unsigned)sz, p);
    free(p);

    if (v.sgn() == -1)
      return -A;
    else
      return A;
  } else
    return APInt(numBits, 0);
}
}

