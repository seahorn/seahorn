#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

#include "seahorn/Analysis/DSA/CallSite.hh"

using namespace llvm;

namespace seahorn
{
  namespace dsa
  { 

     bool DsaCallSite::isPointerTy::operator()(const Value*v) 
     { return v->getType()->isPointerTy();} 

     bool DsaCallSite::isPointerTy::operator()(const Argument&a) 
     { return a.getType()->isPointerTy();} 

     DsaCallSite::DsaCallSite(const ImmutableCallSite &cs)
         : m_cs (cs) { }

     const Value* DsaCallSite::getRetVal () const
     { 
       if (const Function *F = getCallee())
       {
         const FunctionType *FTy = F->getFunctionType ();
         if (!(FTy->getReturnType()->isVoidTy ()))
           return getInstruction();
       }
       return nullptr;
     }

     const Function* DsaCallSite::getCallee () const 
     {
       return m_cs.getCalledFunction();
     }

     const Function* DsaCallSite::getCaller () const 
     {
       return m_cs.getCaller();
     }

     const Instruction* DsaCallSite::getInstruction () const 
     {
       return m_cs.getInstruction();
     }

     DsaCallSite::const_formal_iterator DsaCallSite::formal_begin() const 
     { 
       isPointerTy p;
       assert (getCallee());
       return boost::make_filter_iterator(p, getCallee()->arg_begin(), getCallee()->arg_end());
     }

     DsaCallSite::const_formal_iterator DsaCallSite::formal_end() const 
     { 
       isPointerTy p;
       assert (getCallee());
       return boost::make_filter_iterator(p, getCallee()->arg_end(), getCallee()->arg_end());
     }

      
     DsaCallSite::const_actual_iterator DsaCallSite::actual_begin() const
     { 
       isPointerTy p;
       return boost::make_filter_iterator(p, m_cs.arg_begin(), m_cs.arg_end());
     }

     DsaCallSite::const_actual_iterator DsaCallSite::actual_end() const
     { 
       isPointerTy p;
       return boost::make_filter_iterator(p, m_cs.arg_end(), m_cs.arg_end());
     }

  }
}
