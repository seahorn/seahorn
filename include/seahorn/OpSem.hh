#pragma once

#include "seahorn/SymStore.hh"
#include "ufo/Expr.hpp"
#include "llvm/IR/InstVisitor.h"

namespace seahorn {
using namespace llvm;
using namespace expr;

/// degree of precision of symbolic execution
enum TrackLevel {
  /// numeric registers only
  REG,
  /// registers and pointer addresses (but not content)
  PTR,
  /// memory content
  MEM
};

class OpSem;
class OpSemContext;
using OpSemContextPtr = std::unique_ptr<OpSemContext>;

/// \brief Operational Semantics Context
///
/// The base class for a context (i.e., state) for the operational
/// semantics. Each subclass of OpSem provides it's own implementation
/// of OpSemContext and expects it to be passed when required
class OpSemContext {
private:
  /// A map from symbolic registers to symbolic values
  /// XXX for now lives outside of the context
  SymStore &m_values;

  /// Side-condition to keep extra constraints (e.g., path condition)
  /// XXX for now lives outside of the context
  ExprVector &m_side;

  /// Activation literal for protecting conditions
  Expr m_act;

  Expr m_trueE;
  Expr m_falseE;

public:
  OpSemContext(SymStore &values, ExprVector &side)
      : m_values(values), m_side(side) {
    m_trueE = mk<TRUE>(efac());
    m_falseE = mk<FALSE>(efac());

    m_act = m_trueE;
  }
  OpSemContext(SymStore &values, ExprVector &side, const OpSemContext &o)
      : m_values(o.m_values), m_side(o.m_side), m_act(o.m_act),
        m_trueE(o.m_trueE), m_falseE(o.m_falseE) {}
  OpSemContext(const OpSemContext &) = delete;
  virtual ~OpSemContext() {}

  SymStore &values() { return m_values; }
  Expr read(Expr v) { return m_values.read(v); }
  Expr havoc(Expr v) { return m_values.havoc(v); }
  void write(Expr v, Expr u) { m_values.write(v, u); }

  OpSemContext &act(Expr v) {
    setActLit(v);
    return *this;
  }
  void setActLit(Expr v) { m_act = v; }
  Expr getActLit() const { return m_act; }
  ExprVector &side() { return m_side; }
  void addSideSafe(Expr v) { m_side.push_back(boolop::limp(m_act, v)); }
  void addSide(Expr v) { m_side.push_back(v); }
  void addDef(Expr v, Expr u) { addSide(mk<EQ>(v, u)); }
  void addDefSafe(Expr v, Expr u) { addSideSafe(mk<EQ>(v, u)); }
  void resetSide() { m_side.clear(); }

  ExprFactory &getExprFactory() const { return m_values.getExprFactory(); }
  ExprFactory &efac() const { return getExprFactory(); }

  /// \brief Called when a module is entered
  virtual void onModuleEntry(const Module &M) {}
  /// \brief Called when a function is entered
  virtual void onFunctionEntry(const Function &fn) {}
  /// \brief Called when a function returns
  virtual void onFunctionExit(const Function &fn) {}
  virtual void onBasicBlockEntry(const BasicBlock &bb) {}

  virtual OpSemContextPtr fork(SymStore &values, ExprVector &side) {
    return OpSemContextPtr(new OpSemContext(values, side, *this));
  }
};

/// Information about a function for VC-generation
struct FunctionInfo {
  /// Summary predicate
  Expr sumPred;
  /// Memory region arguments
  SmallVector<const llvm::Value *, 8> regions;
  /// Formal arguments used by the predicate
  SmallVector<const llvm::Argument *, 8> args;
  /// Global variables used by the function
  SmallVector<const llvm::GlobalVariable *, 8> globals;
  /// return value. NULL if the function is void or return is not tracked
  const llvm::Value *ret;

  FunctionInfo() : ret(nullptr) {}

  template <typename OutputIterator>
  void evalArgs(OpSem &sem, SymStore &s, OutputIterator out) const;
};

/// maps llvm::Function to seahorn::FunctionInfo
using FuncInfoMap = DenseMap<const llvm::Function *, FunctionInfo>;

/**
 * Operational Semantics for LLVM instructions and basic blocks.
 * Provides symbolic-executor-like interface by transforming an
 * input symbolic state to an output symbolic state and
 * side-conditions.
 */
class OpSem {
protected:
  ExprFactory &m_efac;
  FuncInfoMap m_fmap;

  Expr trueE;
  Expr falseE;
  Expr m_errorFlag;

public:
  OpSem(ExprFactory &efac)
      : m_efac(efac), trueE(mk<TRUE>(m_efac)), falseE(mk<FALSE>(m_efac)),
        m_errorFlag(
            bind::boolConst(mkTerm<std::string>("error.flag", m_efac))) {}

  OpSem(const OpSem &o)
      : m_efac(o.m_efac), m_fmap(o.m_fmap), m_errorFlag(o.m_errorFlag) {}

  virtual ~OpSem() {}

  ExprFactory &getExprFactory() { return m_efac; }
  ExprFactory &efac() { return m_efac; }

  OpSemContextPtr mkContext(SymStore &values, ExprVector &side) {
    return std::unique_ptr<OpSemContext>(new OpSemContext(values, side));
  }

  /// Executes all instructions in the basic block. Modifies the
  /// store s and returns a side condition. The side-constraints are
  /// optionally conditioned on the activation literal
  virtual void exec(const BasicBlock &bb, OpSemContext &ctx) {
    exec(ctx.values(), bb, ctx.side(), ctx.getActLit());
  }

  /// Executes all phi-instructions on the (from,bb)-edge.
  /// act is an optional activation literal
  virtual void execPhi(const BasicBlock &bb, const BasicBlock &from,
                       OpSemContext &ctx) {
    execPhi(ctx.values(), bb, from, ctx.side(), ctx.getActLit());
  }

  /// Executes a (src,dst) CFG edge
  virtual void execEdg(const BasicBlock &src, const BasicBlock &dst,
                       OpSemContext &ctx) {
    execEdg(ctx.values(), src, dst, ctx.side());
  }

  /// Executes the branch instruction in src that leads to dst
  /// act is an optional activation literal
  virtual void execBr(const BasicBlock &src, const BasicBlock &dst,
                      OpSemContext &ctx) {
    execBr(ctx.values(), src, dst, ctx.side(), ctx.getActLit());
  }

  /// symbolic constant corresponding to the value
  virtual Expr symb(const Value &v) = 0;
  /// value corresponding to the symbolic constant
  virtual const Value &conc(Expr v) = 0;
  /// true if value is tracked
  virtual bool isTracked(const Value &v) = 0;
  /// Expr corresponding to the value in the current store. The
  /// value can be a constant
  virtual Expr lookup(SymStore &s, const Value &v) = 0;
  /// true if all calls to fn will be abstracted
  virtual bool isAbstracted(const Function &fn) { return false; }

  virtual FunctionInfo &getFunctionInfo(const Function &F) {
    return m_fmap[&F];
  }

  virtual bool hasFunctionInfo(const Function &F) const {
    return m_fmap.count(&F) > 0;
  }

  virtual Expr errorFlag(const BasicBlock &BB) { return m_errorFlag; }
  virtual Expr memStart(unsigned id) = 0;
  virtual Expr memEnd(unsigned id) = 0;

  virtual bool isSymReg(Expr v) { return v == m_errorFlag; }

  /// old interface
  virtual void exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
                    Expr act) = 0;

  virtual void execPhi(SymStore &s, const BasicBlock &bb,
                       const BasicBlock &from, ExprVector &side, Expr act) = 0;

  virtual void execEdg(SymStore &s, const BasicBlock &src,
                       const BasicBlock &dst, ExprVector &side) = 0;

  virtual void execBr(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                      ExprVector &side, Expr act) = 0;
};

template <typename OutputIterator>
void FunctionInfo::evalArgs(OpSem &sem, SymStore &s, OutputIterator out) const {
  for (auto *v : regions)
    *out++ = s.read(sem.symb(*v));
  for (auto *a : args)
    *out++ = s.read(sem.symb(*a));
  for (auto *g : globals)
    *out++ = s.read(sem.symb(*g));
  if (ret)
    *out++ = s.read(sem.symb(*ret));
}

} // namespace seahorn
