#ifndef __CFG_HH_
#define __CFG_HH_
/// Extra support for llvm CFG
#include "boost/range/iterator_range.hpp"
#include "boost/iterator/indirect_iterator.hpp"

#include "llvm/IR/CFG.h"

namespace seahorn
{
  using namespace llvm;
  using namespace boost;
  
  inline boost::iterator_range<llvm::succ_iterator>
  succs (llvm::BasicBlock &bb) 
  {return boost::make_iterator_range (succ_begin (&bb), succ_end (&bb));}
  

  inline boost::iterator_range<llvm::const_succ_iterator> 
  succs (const llvm::BasicBlock &bb) 
  {return boost::make_iterator_range (succ_begin (&bb), succ_end (&bb));}

  inline boost::iterator_range<llvm::pred_iterator> 
  preds (llvm::BasicBlock &bb) 
  {return boost::make_iterator_range (pred_begin (&bb), pred_end (&bb));}
  

  inline boost::iterator_range<llvm::const_pred_iterator> 
  preds (const llvm::BasicBlock &bb) 
  {return boost::make_iterator_range (pred_begin (&bb), pred_end (&bb));}
}

#endif
