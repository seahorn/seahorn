#ifndef __DSA_CALLSITE_HH_
#define __DSA_CALLSITE_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/IR/CallSite.h"

#include "boost/iterator/filter_iterator.hpp"

namespace llvm 
{
    class Value;  
    class Function;
    class Instruction;
}

namespace seahorn 
{
  namespace dsa 
  {

    class DsaCallSite {

      struct isPointerTy {
        bool operator()(const llvm::Value*v);
        bool operator()(const llvm::Argument&a);
      };

      const llvm::ImmutableCallSite &m_cs;
      
     public:

      typedef boost::filter_iterator<isPointerTy, 
                                     typename llvm::Function::const_arg_iterator>  
      const_formal_iterator;
      typedef boost::filter_iterator<isPointerTy, 
                                     typename llvm::ImmutableCallSite::arg_iterator>  
      const_actual_iterator;

      DsaCallSite (const llvm::ImmutableCallSite &cs);

      bool operator==(const DsaCallSite &o) const
      { return getInstruction () == o.getInstruction (); }

      const llvm::Value* getRetVal () const; 

      const llvm::Function* getCallee () const; 
      const llvm::Function* getCaller () const; 

      const llvm::Instruction* getInstruction () const;

      const_formal_iterator formal_begin() const; 
      const_formal_iterator formal_end() const; 

      const_actual_iterator actual_begin() const; 
      const_actual_iterator actual_end() const; 
    };
  }
}
#endif 
