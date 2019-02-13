#ifndef __CUTPOINT_GRAPH__H__
#define __CUTPOINT_GRAPH__H__

#include <vector>

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "boost/iterator/indirect_iterator.hpp"
#include "boost/make_shared.hpp"
#include "boost/shared_ptr.hpp"

#include "seahorn/Analysis/TopologicalOrder.hh"
namespace seahorn {
using namespace llvm;

class CutPoint;
class CutPointGraph;

class CpEdge {
  friend class CutPointGraph;

  CutPoint &m_src;
  CutPoint &m_dst;

  typedef std::vector<const BasicBlock *> BlockVector;
  BlockVector m_bbs;

  CutPoint &source() { return m_src; }
  CutPoint &target() { return m_dst; }

public:
  CpEdge(CutPoint &s, CutPoint &d) : m_src(s), m_dst(d) {}

  inline const CutPointGraph &parent() const;
  const CutPoint &source() const { return m_src; }
  const CutPoint &target() const { return m_dst; }

  void push_back(const BasicBlock *b) { m_bbs.push_back(b); }

  typedef boost::indirect_iterator<BlockVector::iterator> iterator;
  typedef boost::indirect_iterator<BlockVector::const_iterator> const_iterator;
  typedef boost::indirect_iterator<BlockVector::reverse_iterator>
      reverse_iterator;
  typedef boost::indirect_iterator<BlockVector::const_reverse_iterator>
      const_reverse_iterator;

  iterator begin() { return boost::make_indirect_iterator(m_bbs.begin()); }
  iterator end() { return boost::make_indirect_iterator(m_bbs.end()); }
  const_iterator begin() const {
    return boost::make_indirect_iterator(m_bbs.begin());
  }
  const_iterator end() const {
    return boost::make_indirect_iterator(m_bbs.end());
  }
  reverse_iterator rbegin() {
    return boost::make_indirect_iterator(m_bbs.rbegin());
  }
  reverse_iterator rend() {
    return boost::make_indirect_iterator(m_bbs.rend());
  }
  const_reverse_iterator rbegin() const {
    return boost::make_indirect_iterator(m_bbs.rbegin());
  }
  const_reverse_iterator rend() const {
    return boost::make_indirect_iterator(m_bbs.rend());
  }
};

class CutPoint {
  friend class CutPointGraph;

  const CutPointGraph &m_parent;
  unsigned m_id;
  const BasicBlock &m_bb;

  typedef SmallVector<CpEdge *, 4> EdgeVector;
  EdgeVector m_pred;
  EdgeVector m_succ;

  void setId(unsigned v) { m_id = v; }

public:
  CutPoint(const CutPointGraph &p, unsigned id, const BasicBlock &bb)
      : m_parent(p), m_id(id), m_bb(bb) {}

  const CutPointGraph &parent() const { return m_parent; }
  unsigned id() const { return m_id; }
  const BasicBlock &bb() const { return m_bb; }

  void addSucc(CpEdge &edg) { m_succ.push_back(&edg); }
  void addPred(CpEdge &edg) { m_pred.push_back(&edg); }

  typedef EdgeVector::iterator iterator;
  typedef EdgeVector::const_iterator const_iterator;
  typedef EdgeVector::reverse_iterator reverse_iterator;
  typedef EdgeVector::const_reverse_iterator const_reverse_iterator;

  iterator succ_begin() { return m_succ.begin(); }
  iterator succ_end() { return m_succ.end(); }

  const_iterator succ_begin() const { return m_succ.begin(); }
  const_iterator succ_end() const { return m_succ.end(); }

  const_iterator pred_begin() const { return m_pred.begin(); }
  const_iterator pred_end() const { return m_pred.end(); }
};

inline CutPoint::const_iterator succ_begin(const CutPoint &cp) {
  return cp.succ_begin();
}

inline CutPoint::const_iterator succ_end(const CutPoint &cp) {
  return cp.succ_end();
}

inline const CutPointGraph &CpEdge::parent() const { return m_src.parent(); }

class CutPointGraph : public FunctionPass {
  typedef boost::shared_ptr<CutPoint> CutPointPtr;

  typedef std::vector<CutPointPtr> CpVector;
  typedef std::vector<boost::shared_ptr<CpEdge>> CpEdgeVector;

  CpVector m_cps;
  CpEdgeVector m_edges;

  typedef DenseMap<const BasicBlock *, BitVector> BlockBitMap;
  /// maps a basic block to ids of cut-points it can forward reach
  BlockBitMap m_fwd;
  /// maps a basic block to ids of cut-points that can reach it
  BlockBitMap m_bwd;

  DenseMap<const BasicBlock *, boost::shared_ptr<CutPoint>> m_bb;

  CutPoint &newCp(const BasicBlock &bb) {
    if (isCutPoint(bb))
      return getCp(bb);

    m_cps.push_back(boost::make_shared<CutPoint>(*this, m_cps.size(), bb));

    m_bb[&bb] = m_cps.back();
    return *(m_cps.back());
  }

  CpEdge &newEdge(CutPoint &s, CutPoint &d) {
    m_edges.push_back(boost::make_shared<CpEdge>(s, d));

    CpEdge &edg = *m_edges.back();

    s.addSucc(edg);
    d.addPred(edg);
    return edg;
  }

  void computeCutPoints(const Function &F, const TopologicalOrder &topo);
  void orderCutPoints(const Function &F, const TopologicalOrder &topo);
  void computeFwdReach(const Function &F, const TopologicalOrder &topo);
  void computeBwdReach(const Function &F, const TopologicalOrder &topo);
  void computeEdges(const Function &F, const TopologicalOrder &topo);

  CpEdge *getEdge(CutPoint &s, CutPoint &d);
  CutPoint &getCp(const BasicBlock &bb) {
    assert(isCutPoint(bb));
    return *(m_bb.find(&bb)->second);
  }

public:
  static char ID;

  CutPointGraph() : FunctionPass(ID) {}

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
  virtual bool runOnFunction(Function &F);
  virtual void releaseMemory() {
    m_cps.clear();
    m_edges.clear();
    m_bb.clear();
  }

  bool isCutPoint(const BasicBlock &bb) const { return m_bb.count(&bb) > 0; }

  // const CutPoint &getCp2 (const BasicBlock &bb) const {return getCp (bb);}

  const CutPoint &getCp(const BasicBlock &bb) const {
    assert(isCutPoint(bb));
    return *(m_bb.find(&bb)->second);
  }

  const CpEdge *getEdge(const CutPoint &s, const CutPoint &d) const;

  /// returns true if the cutpoint can reach the basic block
  /// (without going through other cutpoints
  bool isFwdReach(const CutPoint &cp, const BasicBlock &bb) const;

  typedef boost::indirect_iterator<CpVector::iterator> iterator;
  typedef boost::indirect_iterator<CpVector::const_iterator> const_iterator;
  typedef boost::indirect_iterator<CpVector::reverse_iterator> reverse_iterator;
  typedef boost::indirect_iterator<CpVector::const_reverse_iterator>
      const_reverse_iterator;

  iterator begin() { return make_indirect_iterator(m_cps.begin()); }
  iterator end() { return make_indirect_iterator(m_cps.end()); }
  const_iterator begin() const { return make_indirect_iterator(m_cps.begin()); }
  const_iterator end() const { return make_indirect_iterator(m_cps.end()); }
  reverse_iterator rbegin() { return make_indirect_iterator(m_cps.rbegin()); }
  reverse_iterator rend() { return make_indirect_iterator(m_cps.rend()); }
  const_reverse_iterator rbegin() const {
    return make_indirect_iterator(m_cps.rbegin());
  }
  const_reverse_iterator rend() const {
    return make_indirect_iterator(m_cps.rend());
  }

  const CutPoint &front() const { return *m_cps.front(); }
  const CutPoint &back() const { return *m_cps.back(); }

  void print(raw_ostream &out, const Module *M) const override;

  StringRef getPassName() const override { return "CutPointGraph"; }
};

} // namespace seahorn

#endif
