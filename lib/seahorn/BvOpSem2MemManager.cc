#include "BvOpSem2Context.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {OpSemMemManager::OpSemMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz)
    : m_sem(sem), m_ctx(ctx), m_efac(ctx.getExprFactory()), m_ptrSz(ptrSz),
      m_wordSz(wordSz), m_alignment(m_wordSz) {
  assert((m_wordSz == 1 || m_wordSz == 4 || m_wordSz == 8) &&
         "Untested word size");
  assert((m_ptrSz == 4 || m_ptrSz == 8) && "Untested pointer size");
}
} // namespace details
} // namespace seahorn
