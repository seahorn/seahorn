#ifndef __TOPOLOGICAL_ORDER__HH_
#define __TOPOLOGICAL_ORDER__HH_

#include "llvm/Pass.h"
#include <vector>

#include "llvm/IR/Function.h"

namespace seahorn
{
  using namespace llvm;
  
  /// Constructs topological order of a CFG of a function
  class TopologicalOrder : public FunctionPass
  {
    
    SmallVector<std::pair<const BasicBlock*, const BasicBlock*>, 16 > m_backEdges;
    
    typedef std::vector<const BasicBlock*> BlockVector;
    BlockVector m_order;
    
  public:
    static char ID;
    
    
    TopologicalOrder () : FunctionPass (ID) {}
    
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual bool runOnFunction (Function &F);
    virtual void releaseMemory () 
    {
      m_order.clear ();
      m_backEdges.clear ();
    }
    
    bool isBackEdge (const BasicBlock &src, const BasicBlock &dst) const;
    
    typedef BlockVector::iterator iterator;
    typedef BlockVector::const_iterator const_iterator;
    typedef BlockVector::reverse_iterator reverse_iterator;
    typedef BlockVector::const_reverse_iterator const_reverse_iterator;
   
    iterator begin () { return m_order.begin (); } 
    iterator end () {return m_order.end ();}
    const_iterator begin () const {return m_order.begin ();}
    const_iterator end () const {return m_order.end ();}
    reverse_iterator rbegin () { return m_order.rbegin (); } 
    reverse_iterator rend () {return m_order.rend ();}
    const_reverse_iterator rbegin () const {return m_order.rbegin ();}
    const_reverse_iterator rend () const {return m_order.rend ();}
   
    virtual void print (raw_ostream &out, const Module *m) const;
    virtual const char* getPassName () const {return "TopologicalOrder";}
    
    
  };
  
}


#endif
