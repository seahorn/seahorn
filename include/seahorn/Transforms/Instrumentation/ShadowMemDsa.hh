#pragma once

#include "seahorn/config.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include "seahorn/Expr/Expr.hh"

#include <queue>

namespace seahorn {
namespace shadow_dsa {

using namespace llvm;

/// extracts unique scalar from a call to shadow.mem functions
inline const Value *extractUniqueScalar(ImmutableCallSite cs) {
  if (cs.getCalledFunction()->getName().equals("shadow.mem.global.init"))
    return nullptr;
  assert(cs.arg_size() > 0);
  // -- last argument
  const Value *v = cs.getArgument(cs.arg_size() - 1);

  if (const Instruction *inst = dyn_cast<Instruction>(v)) {
    assert(inst);
    return inst->isCast() ? inst->getOperand(0) : inst;
  } else if (const ConstantPointerNull *c = dyn_cast<ConstantPointerNull>(v))
    return nullptr;
  else if (const ConstantExpr *c = dyn_cast<ConstantExpr>(v))
    return c->getOperand(0);

  return v;
}

inline int64_t getShadowId(const ImmutableCallSite &cs) {
  assert(cs.arg_size() > 0);

  if (const ConstantInt *id = dyn_cast<ConstantInt>(cs.getArgument(0)))
    return id->getZExtValue();

  return -1;
}

/// variable to represent start of a memory region with a given id
inline expr::Expr memStartVar(unsigned id, expr::Expr sort) {
  using namespace expr;
  ExprFactory &efac = sort->efac();
  return bind::mkConst(
      variant::variant(id, mkTerm<std::string>("mem_start", efac)), sort);
}

/// variable to represent end of a memory region with a given id
inline expr::Expr memEndVar(unsigned id, expr::Expr sort) {
  using namespace expr;
  ExprFactory &efac = sort->efac();
  return bind::mkConst(
      variant::variant(id, mkTerm<std::string>("mem_end", efac)), sort);
}

inline bool isShadowMem(const Value &V, const Value **out) {

  // work list
  std::queue<const Value *> wl;
  llvm::DenseSet<const Value *> visited;

  wl.push(&V);
  while (!wl.empty()) {
    const Value *val = wl.front();
    wl.pop();

    if (visited.count(val) > 0)
      continue;
    visited.insert(val);

    if (const CallInst *ci = dyn_cast<const CallInst>(val)) {
      if (const Function *fn = ci->getCalledFunction()) {
        if (!fn->getName().startswith("shadow.mem"))
          return false;
        if (out)
          *out = extractUniqueScalar(ci);
        return true;
      }

      return false;
    } else if (const PHINode *phi = dyn_cast<const PHINode>(val)) {
      for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i)
        wl.push(phi->getIncomingValue(i));
    } else if (const SelectInst *gamma = dyn_cast<const SelectInst>(val)) {
      if (gamma->getName().startswith("seahorn.gsa")) {
        wl.push(gamma->getTrueValue());
        wl.push(gamma->getFalseValue());
      } else
        return false;
    } else
      return false;
  }

  assert(0);
  return false;
}
} // namespace shadow_dsa
} // namespace seahorn
