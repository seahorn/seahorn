#ifndef __SYM_EXEC__HH_
#define __SYM_EXEC__HH_

#include "llvm/IR/InstVisitor.h"
#include "ufo/Expr.hpp"
#include "ufo/ExprLlvm.hpp"
#include "seahorn/SymStore.hh"
#include "seahorn/Analysis/CutPointGraph.hh"

#include "avy/AvyDebug.h"


namespace seahorn
{
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
  
  class SmallStepSymExec;
  
  /// Information about a function for VC-generation
  struct FunctionInfo
  {
    /// Summary predicate
    Expr sumPred;
    /// Memory region arguments
    SmallVector<const llvm::Value*, 8> regions;
    /// Formal arguments used by the predicate
    SmallVector<const llvm::Argument*, 8> args;
    /// Global variables used by the function
    SmallVector<const llvm::GlobalVariable*, 8> globals;
    /// return value. NULL if the function is void or return is not tracked
    const llvm::Value* ret;
    
    FunctionInfo () : ret(NULL) {}
    
    template <typename OutputIterator>
    void evalArgs (SmallStepSymExec &sem, SymStore &s, OutputIterator out) const;
  };
  /// maps llvm::Function to seahorn::FunctionInfo
  typedef DenseMap<const llvm::Function*, FunctionInfo> FuncInfoMap;

  class SmallStepSymExec
  {
  protected:
    ExprFactory &m_efac;
    FuncInfoMap m_fmap;
    
    Expr trueE;
    Expr falseE;
    Expr m_errorFlag;
    
  public:
    SmallStepSymExec (ExprFactory &efac) : 
      m_efac (efac), 
      trueE (mk<TRUE> (m_efac)),
      falseE (mk<FALSE> (m_efac)),
      m_errorFlag (bind::boolConst (mkTerm<std::string> ("error.flag", m_efac))) {}
    
     
    SmallStepSymExec (const SmallStepSymExec &o) : 
      m_efac (o.m_efac), 
      m_fmap (o.m_fmap),
      m_errorFlag (o.m_errorFlag) {}
    
    virtual ~SmallStepSymExec () {}
    
    ExprFactory& getExprFactory () {return m_efac;}
    ExprFactory& efac () {return m_efac;}
    
    /// Executes all instructions in the basic block. Modifies the
    /// store s and returns a side condition. The side-constraints are
    /// optionally conditioned on the activation literal
    virtual void exec (SymStore &s, const BasicBlock &bb,
                       ExprVector &side, Expr act) = 0;
    
    /// Executes a single instruction
    virtual void exec (SymStore &s, const Instruction &inst, 
                       ExprVector &side) = 0;
    
    /// Executes all phi-instructions on the (from,bb)-edge.
    /// act is an optional activation literal
    virtual void execPhi (SymStore &s, const BasicBlock &bb, 
                          const BasicBlock &from, ExprVector &side, Expr act) = 0;
    
    /// Executes a (src,dst) CFG edge
    virtual void execEdg (SymStore &s, const BasicBlock &src,
                          const BasicBlock &dst, ExprVector &side) = 0;
    
    /// Executes the branch instruction in src that leads to dst
    /// act is an optional activation literal
    virtual void execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                         ExprVector &side, Expr act) = 0;
    
    /// symbolic constant corresponding to the value  
    virtual Expr symb (const Value& v) = 0;
    /// value corresponding to the symbolic constant
    virtual const Value& conc (Expr v) = 0;
    /// true if value is tracked
    virtual bool isTracked (const Value& v) = 0;
    /// Expr corresponding to the value in the current store. The
    /// value can be a constant
    virtual Expr lookup (SymStore &s, const Value&v) = 0;
    /// true if all calls to fn will be abstracted
    virtual bool isAbstracted (const Function& fn) { return false; }
    
    virtual FunctionInfo& getFunctionInfo (const Function &F)
    { return m_fmap [ &F ];}
    
    virtual bool hasFunctionInfo (const Function &F) const
    {return m_fmap.count (&F) > 0;}
    
    virtual Expr errorFlag (const BasicBlock &BB) {return m_errorFlag;}
    virtual Expr memStart (unsigned id) = 0;
    virtual Expr memEnd (unsigned id) = 0;
    
  };

  /// -- computes verification condition for a CPG edge
  class LargeStepSymExec 
  {
  public:
    
    virtual ~LargeStepSymExec () {}
    
    /// Execute a CutPoint-to-CutPoint edge
    virtual void execCpEdg (SymStore &s, const CpEdge &edg, ExprVector &side) = 0;
  };
  
 
  /// Small step symbolic execution for integers
  /// Highly non-deterministic. Used to identify live symbols
  class IntLightSymExec : public SmallStepSymExec
  { 
  public:
    IntLightSymExec (ExprFactory &efac) : SmallStepSymExec (efac) {} 
    
    /// Execute all instructions in the basic block. Modifies the
    /// store s and stores side condition in side
    virtual void exec (SymStore &s, const BasicBlock &bb, 
                       ExprVector &side);
    
    /// Executes a single instruction
    virtual void exec (SymStore &s, const Instruction &inst, 
                       ExprVector &side);
    
    /// Executes all phi-instructions on the (from,bb)-edge.
    virtual void execPhi (SymStore &s, const BasicBlock &bb, 
                          const BasicBlock &from, ExprVector &side);
    
    virtual void execEdg (SymStore &s, const BasicBlock &src,
                          const BasicBlock &dst, ExprVector &side);
    virtual void execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                         ExprVector &side);
    virtual Expr symb (const Value &I);
    virtual const Value &conc (Expr v);
    virtual bool isTracked (const Value &v);
    virtual Expr lookup (SymStore &s, const Value &v);
    
  };
    
  template <typename OutputIterator>
  void FunctionInfo::evalArgs (SmallStepSymExec &sem, SymStore &s, 
                               OutputIterator out) const
  {
    for (auto *v : regions) *out++ = s.read (sem.symb (*v));
    for (auto *a : args) *out++ = s.read (sem.symb (*a));
    for (auto *g : globals) *out++ = s.read (sem.symb (*g));
    if (ret) *out++ = s.read (sem.symb (*ret));
  }


}



#endif 

