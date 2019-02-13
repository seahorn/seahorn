///
/// class TaintAnalysis
///

#ifndef _TAINT_ANALYSIS__H_
#define _TAINT_ANALYSIS__H_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "ufo/Expr.hpp"

#include "ufo/Smt/EZ3.hh"
#include "ufo/Smt/Z3n.hpp"

#include "seahorn/HornifyModule.hh"

#include <memory>
#include <vector>

namespace seahorn
{
    using namespace llvm;

    class TaintAnalysis
    {
    public:
        /// Constructor for stand-alone mode
        TaintAnalysis (unsigned nBound) : m_nBound(nBound)
        {

        }

        virtual ~TaintAnalysis ()
        {}

        bool checkTaint(HornifyModule &hm);

    private:
        void printCex(ZFixedPoint<EZ3> &fp);

    private:
        unsigned m_nBound;
    };

    class TaintAnalysisPass : public llvm::ModulePass
    {
    public:
        static char ID;
        /// Constructor for stand-alone mode
        TaintAnalysisPass (unsigned nBound)
        : ModulePass(ID) ,
          m_TaintAnalysis(nBound),
          m_nBound(nBound)
        {

        }


        virtual ~TaintAnalysisPass ()
        {}

        /// Entry point in stand-alone mode
        virtual bool runOnModule (Module &M);
        virtual void getAnalysisUsage (AnalysisUsage &AU) const;
        virtual StringRef getPassName () const {return "TaintAnalysisPass";}

    private:
        TaintAnalysis m_TaintAnalysis;
        unsigned m_nBound;
    };
}


#endif /* _TAINT_ANALYSIS__H_ */
