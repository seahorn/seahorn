#pragma once
#include "seahorn/SymStore.hh"
#include "ufo/Expr.hpp"

#include "llvm/IR/InstVisitor.h"
#include <memory>

namespace seahorn {
/// \brief degree of precision of symbolic execution
enum TrackLevel {
  /// \brief Ignore all but integer registers
  REG,
  /// \brief Ignore all bu integer and pointer typed registers
  PTR,
  /// \brief Track integer and pointer registers and memory content
  MEM
};

// -- forward declarations
class OpSemContext;
using OpSemContextPtr = std::unique_ptr<OpSemContext>;

/// \brief Operational Semantics Context
///
/// The base class for a context (i.e., state) for the operational
/// semantics. Each subclass of OpSem provides it's own implementation
/// of OpSemContext and expects it to be passed when required
class OpSemContext {
private:
  /// \brief A map from symbolic registers to symbolic values
  /// XXX The context keeps a reference to the store. The store itself lives outside of the context
  /// XXX This is a temporary measure to keep new and old implementations together
  SymStore &m_values;

  /// \brief Side-condition to keep extra constraints (e.g., path condition)
  /// XXX The context keeps a reference to the side condition.
  /// XXX The side condition itself lives outside of the context.
  /// XXX This is a temporary measure to keep new and old implementations together
  ExprVector &m_side;

  /// \brief Activation literal for protecting conditions
  Expr m_act;

protected:
  // -- cached values

  /// Constant true
  Expr m_trueE;
  /// Constant false
  Expr m_falseE;

public:
  /// \brief Creates a new \c OpSemContext with given values and side condition
  ///
  /// TODO: Currently values and side are stored outside of the context
  OpSemContext(SymStore &values, ExprVector &side)
      : m_values(values), m_side(side) {
    m_trueE = mk<TRUE>(efac());
    m_falseE = mk<FALSE>(efac());

    m_act = m_trueE;
  }
  /// \brief Copy constructor with optionally new \p values and \p side
  OpSemContext(SymStore &values, ExprVector &side, const OpSemContext &o)
      : m_values(o.m_values), m_side(o.m_side), m_act(o.m_act),
        m_trueE(o.m_trueE), m_falseE(o.m_falseE) {}
  OpSemContext(const OpSemContext &) = delete;
  virtual ~OpSemContext() = default;

  /// Returns reference to the symbolic store
  SymStore &values() { return m_values; }
  /// Returns the current value of a given register/expression in the store
  Expr read(Expr v) { return m_values.read(v); }
  /// Writes a non-deterministic value at a given register
  Expr havoc(Expr v) { return m_values.havoc(v); }
  /// Writes a given value at a given register
  void write(Expr v, Expr u) { m_values.write(v, u); }

  /// Sets an expression to be used as an activation literal
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

  // -- event handlers
  /// \brief Called when a module is entered
  virtual void onModuleEntry(const llvm::Module &M) {}
  /// \brief Called when a function is entered
  virtual void onFunctionEntry(const llvm::Function &fn) {}
  /// \brief Called when a function returns
  virtual void onFunctionExit(const llvm::Function &fn) {}
  /// \brief Called when a basic block is entered
  virtual void onBasicBlockEntry(const llvm::BasicBlock &bb) {}

  /// \brief Fork context using given symbolic store and a side condition
  virtual OpSemContextPtr fork(SymStore &values, ExprVector &side) {
    return OpSemContextPtr(new OpSemContext(values, side, *this));
  }
};

/// \brief Tracks information about a function
/// Used to generate function summaries during vcgen
/// TODO: needs tlc
struct FunctionInfo {
  /// Summary predicate
  Expr sumPred;
  /// Memory region arguments
  llvm::SmallVector<const llvm::Value *, 8> regions;
  /// Formal arguments used by the predicate
  llvm::SmallVector<const llvm::Argument *, 8> args;
  /// Global variables used by the function
  llvm::SmallVector<const llvm::GlobalVariable *, 8> globals;
  /// return value. NULL if the function is void or return is not tracked
  const llvm::Value *ret = nullptr;

  FunctionInfo() = default;
};

class OperationalSemantics {
protected:
  ExprFactory &m_efac;

  /// maps llvm::Function to seahorn::FunctionInfo
  using FuncInfoMap = llvm::DenseMap<const llvm::Function *, FunctionInfo>;
  FuncInfoMap m_fmap;

  Expr trueE;
  Expr falseE;
  Expr m_errorFlag;

public:
  explicit OperationalSemantics(ExprFactory &efac)
      : m_efac(efac), trueE(mk<TRUE>(m_efac)), falseE(mk<FALSE>(m_efac)),
        m_errorFlag(
            bind::boolConst(mkTerm<std::string>("error.flag", m_efac))) {}

  explicit OperationalSemantics(const OperationalSemantics &o)
      : m_efac(o.m_efac), m_fmap(o.m_fmap), m_errorFlag(o.m_errorFlag) {}

  virtual ~OperationalSemantics() = default;

  ExprFactory &getExprFactory() const { return m_efac; }
  ExprFactory &efac() const { return m_efac; }

  /// \brief Create context/state for OpSem using given symstore and side
  /// Sub-classes can override it to customize the context
  virtual OpSemContextPtr mkContext(SymStore &values, ExprVector &side) {
    return std::unique_ptr<OpSemContext>(new OpSemContext(values, side));
  }

  /// \brief Executes all instructions (except for PHINode) of a given
  /// basic block
  virtual void exec(const llvm::BasicBlock &bb, OpSemContext &ctx) = 0;

  /// \brief Executes all PHINode instructions in \bb assuming that
  /// previously executing basic block was \p from
  virtual void execPhi(const llvm::BasicBlock &bb, const llvm::BasicBlock &from,
                       OpSemContext &ctx) = 0;

  /// \brief Executes all instructions of \p src (excluding PHINode)
  /// and all PHINode instructions of \p dst
  virtual void execEdg(const llvm::BasicBlock &src, const llvm::BasicBlock &dst,
                       OpSemContext &ctx) = 0;

  /// \brief Execute the branch instruction of \p src assuming that
  /// control flows to \p dst. Side condition is extended with the
  /// symbolic value of the branch condition (if any)
  virtual void execBr(const llvm::BasicBlock &src, const llvm::BasicBlock &dst,
                      OpSemContext &ctx) = 0;

  /// \brief Returns a symbolic register correspond to llvm::Value \p v
  ///
  /// Creates a new register if one does not exists
  virtual Expr mkSymbReg(const llvm::Value &v, OpSemContext &ctx) = 0;

  /// \brief Returns a symbolic register corresponding to llvm::Value \p v
  ///
  /// Returns null expression if the value has no corresponding symbolic register
  virtual Expr getSymbReg(const llvm::Value &v, const OpSemContext &ctx) const = 0;

  /// \brief Returns an llvm::Value corresponding to a symbolic
  /// register
  virtual const llvm::Value &conc(Expr v) const = 0;
  /// \brief Returns true if \p v is tracked by the semantics If \p v
  /// is not tracked, it is assumed that it is not executed (if an
  /// instruction) and that it does not influence a value of any
  /// instruction that is tracked.
  virtual bool isTracked(const llvm::Value &v) const = 0;
  /// \brief Returns a symbolic value of \p v in the given store \p s
  /// \p v is either a constant or has a corresponding symbolic
  /// register
  virtual Expr lookup(SymStore &s, const llvm::Value &v) = 0;

  /// \brief Returns true if the semantics ignores a call to the given
  /// function
  virtual bool isAbstracted(const llvm::Function &fn) { return false; }

  virtual FunctionInfo &getFunctionInfo(const llvm::Function &F) {
    return m_fmap[&F];
  }

  virtual bool hasFunctionInfo(const llvm::Function &F) const {
    return m_fmap.count(&F) > 0;
  }

  /// \brief Returns special symbolic register that represents that an
  /// error has occurred
  virtual Expr errorFlag(const llvm::BasicBlock &BB) { return m_errorFlag; }

  // -- legacy functions necessary during refactoring

  /// \brief Returns true if \p v is a symbolic register known to this
  /// OpSem object
  virtual bool isSymReg(Expr v) { return v == m_errorFlag; }

};

} // namespace seahorn
