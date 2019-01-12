#include "seahorn/LiveSymbols.hh"
#include "boost/range.hpp"
#include "boost/range/algorithm.hpp"
#include "seahorn/Support/SeaDebug.h"
#include "ufo/ExprLlvm.hpp"

#include "seahorn/Support/SortTopo.hh"
#include "llvm/Analysis/CFG.h"

namespace seahorn {

void LiveInfo::setLive(const ExprVector &l) {
  m_live.assign(l.begin(), l.end());
  boost::sort(m_live);
}

void LiveInfo::setDefs(const ExprVector &d) {
  m_defs.assign(d.begin(), d.end());
  boost::sort(m_defs);
}

void LiveInfo::addEdgeDef(const ExprVector &d) {
  m_edgeDefs.push_back(ExprVector());
  ExprVector &defs = m_edgeDefs.back();
  defs.assign(d.begin(), d.end());
  boost::sort(defs);
}

void LiveInfo::addLive(ExprVector &v) {
  if (v.size() == 0)
    return;

  boost::sort(v);
  size_t sz = m_live.size();
  m_live.reserve(sz + v.size());

  boost::copy(v, std::back_inserter(m_live));
  std::inplace_merge(m_live.begin(), m_live.begin() + sz, m_live.end());
}

/// like add live but v might contain already live variables
void LiveInfo::unionLive(ExprVector &v) {
  boost::sort(v);
  ExprVector newLive;
  newLive.reserve(v.size());
  boost::set_difference(v, m_live, std::back_inserter(newLive));
  addLive(newLive);
}

void LiveSymbols::run() {
  // -- compute def/use for each basic block
  localPass();
  // -- for all functions except main, add extra use of arguments
  // -- and global variables at function exit. This is needed for
  // -- summary computation.
  if (!m_f.getName().equals("main"))
    patchArgsAndGlobals();
  // -- propagate local def/use over the CFG.
  globalPass();

  // HACK: skip main() because it is not treated as a function (i.e., no
  // summary)
  if (m_f.getName().equals("main"))
    return;

  // -- anything that is live at entry should be live at every block
  // -- reachable from entry
  ExprVector liveAtEntry(live(&m_f.getEntryBlock()));
  globallyLive(liveAtEntry);
}

void LiveSymbols::dump() const {
  errs() << "Function: " << m_f.getName() << "\n";
  for (auto &entry : m_liveInfo)
    errs() << entry.first->getName() << ": " << entry.second.live().size()
           << "\n";
}

void LiveSymbols::patchArgsAndGlobals() {
  LiveInfo &li = m_liveInfo[&m_f.getEntryBlock()];

  ExprVector extras;

  for (Expr v : li.live()) {
    assert(bind::isFapp(v));
    Expr u = bind::fname(bind::fname(v));
    if (!isOpX<VALUE>(u))
      continue;

    const Value *val = getTerm<const Value *>(u);

    if (isa<Argument>(val) || isa<GlobalVariable>(val))
      extras.push_back(v);
  }

  // find block with return and make extras live there
  for (const BasicBlock *bb : m_rtopo)
    if (isa<ReturnInst>(bb->getTerminator())) {
      m_liveInfo[bb].addLive(extras);
      break;
    }
}

void LiveSymbols::localPass() {
  RevTopoSort(m_f, m_rtopo);

  for (const BasicBlock *bb : m_rtopo) {
    LiveInfo &li = m_liveInfo[bb];

    // // -- no live variables at any terminal basic block of the main function
    // if (llvm::succ_begin (bb) == llvm::succ_end (bb) &&
    //     m_f.getName ().equals ("main")) continue;

    SymStore s(m_gstore, true);
    OpSemContextPtr ctx = m_sem.mkContext(s, m_side);
    // -- execute the basic block and the condition of the terminator
    symExec(*ctx, *bb);

    LOG("live", errs() << "After executing " << bb->getName() << "\n"
                       << "Got live vars: " << s.uses().size() << "\n";
        for (auto i
             : s.uses()) { errs() << *i << " "; } errs()
        << "\n";);

    // -- live and defs based on what is read/written by symbolic execution
    li.setLive(s.uses());
    li.setDefs(s.defs());

    // -- execute phi-nodes on the edges and update block's live
    // -- symbols and edge definitions
    for (const llvm::BasicBlock *succ : llvm::successors(bb)) {
      SymStore ss(m_gstore, true);
      OpSemContextPtr cctx = m_sem.mkContext(ss, m_side);
      // -- execute the phi-nodes
      symExecPhi(*cctx, *succ, *bb);

      LOG("live", errs() << "After executing phiNodes on the edge: "
                         << bb->getName() << "->" << succ->getName() << " got "
                         << ss.uses().size() << " uses\n";
          for (auto i
               : ss.uses()) { errs() << *i << " "; } errs()
          << "\n";);
      li.addEdgeDef(ss.defs());

      // compute extra live variables by finding new uses at the edge
      ExprVector uses(ss.uses().size());
      boost::copy(ss.uses(), uses.begin());
      boost::sort(uses);

      ExprVector uses2;
      uses2.reserve(uses.size());
      boost::set_difference(uses, li.defs(), std::back_inserter(uses2));
      uses.clear();
      boost::set_difference(uses2, li.live(), std::back_inserter(uses));
      li.addLive(uses);
    }
    // -- at this point local live information for bb is computed
  }
  // -- at this point all local live information is computed for all
  // -- basic blocks. Can update global uses.
}

void LiveSymbols::globalPass() {
  // -- propagate live symbol information until nothing can be propagated
  // -- based on local live symbol information computed by initialize()
  bool dirty;
  do {
    dirty = false;
    for (const BasicBlock *src : m_rtopo) {
      unsigned idx = 0;
      LiveInfo &srcLi = m_liveInfo[src];

      for (const BasicBlock *dst :
           boost::make_iterator_range(succ_begin(src), succ_end(src))) {
        LiveInfo &dstLi = m_liveInfo[dst];

        ExprVector live;
        live.reserve(dstLi.live().size());

        ExprVector live2;
        live2.reserve(live.size());

        boost::set_difference(dstLi.live(), srcLi.edge_defs(idx++),
                              std::back_inserter(live));
        boost::set_difference(live, srcLi.defs(), std::back_inserter(live2));

        live.clear();
        boost::set_difference(live2, srcLi.live(), std::back_inserter(live));

        if (!live.empty()) {
          dirty = true;
          srcLi.addLive(live);
        }
      }
    }
  } while (dirty);
}

void LiveSymbols::symExec(OpSemContext &ctx, const BasicBlock &bb) {
  m_sem.exec(bb, ctx);
  m_side.clear();
}

void LiveSymbols::symExecPhi(OpSemContext &ctx, const BasicBlock &bb,
                             const BasicBlock &from) {
  m_sem.execPhi(bb, from, ctx);
  m_side.clear();
}

const ExprVector &LiveSymbols::live(const BasicBlock *bb) const {
  auto it = m_liveInfo.find(bb);
  assert(it != m_liveInfo.end());
  return it->second.live();
}

void LiveSymbols::globallyLive(ExprVector &live) {
  for (auto &kv : m_liveInfo)
    kv.second.unionLive(live);
}
} // namespace seahorn
