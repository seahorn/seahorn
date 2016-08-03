#include "seahorn/Transforms/Scalar/LowerGvInitializers.hh"

#include "boost/range.hpp"

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"

namespace seahorn
{
  char LowerGvInitializers::ID = 0;
  
  bool LowerGvInitializers::runOnModule (Module &M) {

    const DataLayout* DL = &getAnalysis<DataLayoutPass>().getDataLayout ();

    Function *f = M.getFunction ("main");
    if (!f) return false;
    
    IRBuilder<> Builder (f->getContext ());
    
    Builder.SetInsertPoint (&f->getEntryBlock (), 
                            f->getEntryBlock ().begin ());

    bool change=false;
    for (GlobalVariable &gv : boost::make_iterator_range (M.global_begin (),
                                                          M.global_end ()))
    {
      if (!gv.hasInitializer ()) continue;
      PointerType *ty = dyn_cast<PointerType> (gv.getType ());
      if (!ty) continue;
      Type *ety = ty->getElementType ();
      // only deal with scalars for now
      if (ety->isIntegerTy () || ety->isPointerTy ())
      {
      
        // -- create a store instruction
        Builder.CreateAlignedStore (gv.getInitializer (), &gv, 
                                    DL->getABITypeAlignment (ety));
        change=true;
      }
      else
        errs () << "WARNING: Ignoring initializer for" << gv << "\n";
    }
      
    return change;
  }

}

static llvm::RegisterPass<seahorn::LowerGvInitializers>
X ("lower-gv-init", "Lower initialization of global variables");
