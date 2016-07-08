#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Analysis/DSA/Info.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Graph.hh"

#include "boost/range.hpp"

using namespace seahorn::dsa;
using namespace llvm;

void Info::getAnalysisUsage (AnalysisUsage &AU) const {
  AU.addRequired<DataLayoutPass> ();
  AU.addRequired<TargetLibraryInfo> ();
  AU.addRequired<Global> ();
  AU.setPreservesAll ();
}

static bool isStaticallyKnown (const DataLayout* dl, 
                               const TargetLibraryInfo* tli,
                               const Value* v) 
{
  uint64_t size;
  if (getObjectSize (v, size, dl, tli, true))
    return (size > 0);
  return false; 
}

void Info::addMemoryAccess (const Value* v) 
{
  v = v->stripPointerCasts();
  if (!m_g->hasCell(*v)) {
    // sanity check
    if (v->getType()->isPointerTy())
      errs () << "DsaInfo: pointer value " << *v << " has not cell\n";
    return;
  }
  
  const Cell &c = m_g->getCell (*v);

  Node *n = c.getNode();
  auto it = m_nodes_map.find (n);
  if (it != m_nodes_map.end () && !isStaticallyKnown (m_dl, m_tli, v))
    ++(it->second);

}        

void Info::countMemoryAccesses (Module &M) 
{
  // A node can be read or modified even if there is no a memory
  // load/store for it. This can happen after nodes are unified.
  // 
  // Here we just count the number of **non-trivial** memory
  // loads/stores because it is useful for passes that will instrument
  // them.
  for (auto &F: M) {
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
      const Instruction *I = &*i;
      if (const LoadInst *LI = dyn_cast<LoadInst>(I)) {
        addMemoryAccess (LI->getPointerOperand ());
      } else if (const StoreInst *SI = dyn_cast<StoreInst>(I)) {
        addMemoryAccess (SI->getPointerOperand ());
      } else if (const MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
        addMemoryAccess (MTI->getDest ());
        addMemoryAccess (MTI->getSource ());
      } else if (const MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
        addMemoryAccess (MSI->getDest ());
      }
    }
  }
}
      
void Info::printMemoryAccesses (NodeInfoVector &nodes, llvm::raw_ostream &o) 
{
  unsigned int total_accesses = 0;
  for (auto &n: nodes) 
    total_accesses += n.getAccesses();

  o << nodes.size ()  << " Total number of read and/or modified nodes.\n";      
  o << total_accesses << " Total number of memory load/stores.\n";     
  
  //  --- Print a summary of accesses
  unsigned int summ_size = 5;
  o << "Summary of the " << summ_size  << " nodes with more load/stores:\n";
  std::sort (nodes.begin (), nodes.end (),
             [](NodeInfo n1, NodeInfo n2)
             { return (n1.getAccesses() > n2.getAccesses());});
               
  if (total_accesses > 0) {
    for (auto &n: nodes) {
      if (summ_size <= 0) break;
      summ_size--;
      if (n.getAccesses() == 0) break;
      o << "  [Node Id " << n.getId()  << "] " 
             << n.getAccesses() << " (" << (int) (n.getAccesses() * 100 / total_accesses) 
             << "%) of total memory load/stores\n" ;
    }
    o << "  ...\n";
  }
}

void Info::printMemoryTypes (NodeInfoVector &nodes, llvm::raw_ostream& o) 
{
  unsigned num_collapses = 0;
  unsigned num_typed_nodes = 0;
  for (auto &n: nodes) {
    num_collapses += n.getNode()->isCollapsed ();
    num_typed_nodes += (std::distance(n.getNode()->types().begin(),
                                      n.getNode()->types().end()) > 0);
  }
  o << num_typed_nodes << "  Total number of typed nodes.\n";
  o << num_collapses << "  Total number of collapsed nodes.\n";

  // TODO: print all node's types
}

void Info::printMemoryAllocSites (NodeInfoVector &nodes, llvm::raw_ostream& o) 
{
  // Assign a unique (deterministic) id to each allocation site
  unsigned id = 0;
  typedef boost::container::flat_set<NodeInfo> NodeInfoSet;
  // map each allocation site to a set of nodes
  DenseMap<const llvm::Value*, std::pair<unsigned, NodeInfoSet> > alloc_map;
  // iterate over all nodes
  for (auto &n: nodes) {
    // iterate over all allocation sites
    for (const llvm::Value*v : boost::make_iterator_range(n.getNode()->begin(),
                                                          n.getNode()->end())) {
      auto it = alloc_map.find (v);
      if (it != alloc_map.end()) {
        it->second.second.insert(n);
      } else {
        NodeInfoSet s;
        s.insert(n);
        alloc_map.insert(std::make_pair(v, std::make_pair(++id, s)));
      }
    }
  }

  o << alloc_map.size() << "  Total number of allocation sites\n";
  // TODO: print allocation sites ordered by id
  for (auto &kv: alloc_map) {
    o << "  [Alloc site Id " << kv.second.first << " DSNode Ids {";
    bool first = true;
    for (typename NodeInfoSet::iterator it = kv.second.second.begin(),
             et = kv.second.second.end(); it != et; ) {
      if (!first) o << ",";
      else first = false;
      o << it->getId ();
      ++it;
    }
    o << "}]  " << *(kv.first) << "\n";
  }

}

bool Info::runOnModule (Module &M) {

  m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
  m_tli = &getAnalysis<TargetLibraryInfo> ();
  m_g = &getAnalysis<Global>().getGraph();
 
  // -- Assign a unique (deterministic) id to each node
  //    Important: the order of [ m_g->begin()...m_g->end() ) must be
  //    deterministic. Otherwise, we will assign node id's that will
  //    change from one execution to another.
  unsigned node_id = 0; 
  for (auto const& n: boost::make_iterator_range(m_g->begin(), m_g->end()))
    m_nodes_map.insert(std::make_pair(&n, NodeInfo(&n, ++node_id)));

  countMemoryAccesses(M);

  // --- filter out dead nodes
  // XXX: we should use remove_if but DenseMap does not implement all
  // functionality needed.
  NodeInfoVector live_nodes;
  live_nodes.reserve (m_nodes_map.size ());
  for (auto &kv: m_nodes_map) 
    if (kv.second.getNode()->isRead() || kv.second.getNode()->isModified()) 
      live_nodes.push_back (kv.second); 


  errs () << " ========== Begin Dsa info  ==========\n";

  printMemoryAccesses (live_nodes, llvm::errs());
  printMemoryTypes (live_nodes, llvm::errs());
  printMemoryAllocSites (live_nodes, llvm::errs());
  
  errs () << " ========== End Dsa info  ==========\n";

  return false;
}

char Info::ID = 0;

static llvm::RegisterPass<Info> 
X ("dsa-info", "Collect stats and information for dsa clients");
