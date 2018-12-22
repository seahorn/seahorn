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
protected:
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

  /// \brief Fork context using given symbolic store and a side condition
  virtual OpSemContextPtr fork(SymStore &values, ExprVector &side) {
    return OpSemContextPtr(new OpSemContext(values, side, *this));
  }
};

/// \brief Tracks information about a function
/// Used to generate function summaries during vcgen
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


/// \brief Abstract interface for Operational Semantics
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

  /// \brief Create context/state for OpSem using given symstore and side
  /// Sub-classes can override it to customize the context
  virtual OpSemContextPtr mkContext(SymStore &values, ExprVector &side) {
    return std::unique_ptr<OpSemContext>(new OpSemContext(values, side));
  }

  /// \brief Executes all instructions (except for PHINode) of a given
  /// basic block
  virtual void exec(const BasicBlock &bb, OpSemContext &ctx) {
    exec(ctx.values(), bb, ctx.side(), ctx.getActLit());
  }

  /// \brief Executes all PHINode instructions in \bb assuming that
  /// previously executing basic block was \p from
  virtual void execPhi(const BasicBlock &bb, const BasicBlock &from,
                       OpSemContext &ctx) {
    execPhi(ctx.values(), bb, from, ctx.side(), ctx.getActLit());
  }

  /// \brief Executes all instructions of \p src (excluding PHINode)
  /// and all PHINode instructions of \p dst
  virtual void execEdg(const BasicBlock &src, const BasicBlock &dst,
                       OpSemContext &ctx) {
    execEdg(ctx.values(), src, dst, ctx.side());
  }

  /// \brief Execute the branch instruction of \p src assuming that
  /// control flows to \p dst. Side condition is extended with the
  /// symbolic value of the branch condition (if any)
  virtual void execBr(const BasicBlock &src, const BasicBlock &dst,
                      OpSemContext &ctx) {
    execBr(ctx.values(), src, dst, ctx.side(), ctx.getActLit());
  }

  /// \brief Returns a symbolic register correspond to llvm::Value
  /// Deprecated. See mkSymbReg
  virtual Expr symb(const Value &v) = 0;

  /// \brief Returns a symbolic register correspond to llvm::Value
  virtual Expr mkSymbReg(const Value &v, OpSemContext &ctx) {
    return symb(v);
  }

  /// \brief Returns an llvm::Value corresponding to a symbolic
  /// register
  virtual const Value &conc(Expr v) = 0;
  /// \brief Returns true if \p v is tracked by the semantics If \p v
  /// is not tracked, it is assumed that it is not executed (if an
  /// instruction) and that it does not influence a value of any
  /// instruction that is tracked.
  virtual bool isTracked(const Value &v) = 0;
  /// \brief Returns a symbolic value of \p v in the given store \p s
  /// \p v is either a constant or has a corresponding symbolic
  /// register
  virtual Expr lookup(SymStore &s, const Value &v) = 0;

  /// \brief Returns true if the semantics ignores a call to the given
  /// function
  virtual bool isAbstracted(const Function &fn) { return false; }

  virtual FunctionInfo &getFunctionInfo(const Function &F) {
    return m_fmap[&F];
  }

  virtual bool hasFunctionInfo(const Function &F) const {
    return m_fmap.count(&F) > 0;
  }

  /// \brief Returns special symbolic register that represents that an
  /// error has occurred
  virtual Expr errorFlag(const BasicBlock &BB) { return m_errorFlag; }

  /// \brief Returns special symbolic register that contains the value
  /// at which memory region with id \p id begins
  virtual Expr memStart(unsigned id) = 0;
  /// \brief Returns special symbolic register that contains the value
  /// at which memory region with id \p id ends
  virtual Expr memEnd(unsigned id) = 0;

  /// \brief Returns true if \p v is a symbolic register known to this
  /// OpSem object
  virtual bool isSymReg(Expr v) { return v == m_errorFlag; }

  /// Deprecated old interface
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
