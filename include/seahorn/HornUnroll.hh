///
/// class HornUnroll
///

#ifndef _HORN_UNROLL__H_
#define _HORN_UNROLL__H_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "ufo/Expr.hpp"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include "ufo/Smt/EZ3.hh"
#include "ufo/Smt/Z3n.hpp"

#include <memory>
#include <vector>

namespace seahorn {
using namespace llvm;

class HornUnroll //: public llvm::ModulePass
{
public:
  /// Constructor for stand-alone mode
  HornUnroll(bool bStrict = false) : m_bStrict(bStrict) {}

  HornClauseDB &getHornClauseDB() { return *m_pUnrolledDB; }

  virtual ~HornUnroll() {}

  void unroll(unsigned nBound, HornifyModule &hm, HornClauseDB &db);

private:
  bool m_bStrict;
  std::shared_ptr<HornClauseDB> m_pUnrolledDB;
};

class HornUnrollPass : public llvm::ModulePass {
public:
  static char ID;
  /// Constructor for stand-alone mode
  HornUnrollPass(unsigned nBound, bool bStrict = false)
      : ModulePass(ID), m_HornUnroll(bStrict), m_nBound(nBound) {}

  virtual ~HornUnrollPass() {}

  /// Entry point in stand-alone mode
  virtual bool runOnModule(Module &M);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
  virtual const char *getPassName() const { return "HornUnrollPass"; }

  void unroll();

private:
  HornUnroll m_HornUnroll;
  unsigned m_nBound;
};
} // namespace seahorn

#endif /* _HORN_UNROLL__H_ */
