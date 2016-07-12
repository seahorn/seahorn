#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Analysis/DSA/Info.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Graph.hh"

#include "boost/range.hpp"

using namespace seahorn::dsa;
using namespace llvm;

static llvm::cl::opt<bool>
DsaInfoDetails("new-dsa-info-details",
    llvm::cl::desc ("Print Dsa info details"),
    llvm::cl::init (false),
    llvm::cl::Hidden);

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
  // Here we just count the number of **non-trivial** memory accesses
  // because it is useful for passes that will instrument them.
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
  o << " --- Access information\n";

  unsigned int total_accesses = 0;
  for (auto &n: nodes) 
    total_accesses += n.getAccesses();

  o << "\t" << nodes.size ()  << " number of read and modified nodes.\n";      
  o << "\t" << total_accesses << " number of non-trivial memory accesess (load/store/memcpy/memset/memmove).\n";     
  
  //  --- Print a summary of accesses
  unsigned int summ_size = 5;
  o << "\t Summary of the " << summ_size  << " nodes with more accesses:\n";
  std::sort (nodes.begin (), nodes.end (),
             [](NodeInfo n1, NodeInfo n2)
             { return (n1.getAccesses() > n2.getAccesses());});
               
  if (total_accesses > 0) {
    for (auto &n: nodes) {
      if (summ_size <= 0) break;
      summ_size--;
      if (n.getAccesses() == 0) break;
      o << "\t  [Node Id " << n.getId()  << "] " 
             << n.getAccesses() << " (" << (int) (n.getAccesses() * 100 / total_accesses) 
             << "%) of total memory accesses\n" ;
    }
  }
}

void Info::printMemoryTypes (NodeInfoVector &nodes, llvm::raw_ostream& o) 
{
  o << " --- Type information\n";
  unsigned num_collapses = 0;
  unsigned num_typed_nodes = 0;
  for (auto &n: nodes) {
    num_collapses += n.getNode()->isCollapsed ();
    num_typed_nodes += (std::distance(n.getNode()->types().begin(),
                                      n.getNode()->types().end()) > 0);
  }
  o << "\t" << num_typed_nodes << " number of typed nodes.\n";
  o << "\t" << num_collapses << " number of collapsed nodes.\n";

  // TODO: print all node's types
}

void Info::printMemoryAllocSites (NodeInfoVector &nodes, llvm::raw_ostream& o) 
{
  o << " --- Allocation site information\n";

  // Assign a unique (deterministic) id to each allocation site
  unsigned id = 0;

  // map each allocation site to a set of nodes
  typedef boost::container::flat_set<NodeInfo> NodeInfoSet;
  DenseMap<const llvm::Value*, std::pair<unsigned, NodeInfoSet> > alloc_map;

  // number of nodes without allocation sites
  unsigned num_orphan_nodes = 0;
  // number of checks belonging to orphan nodes.
  unsigned num_orphan_checks = 0;
  // keep track of maximum number of allocation sites in a single node
  unsigned max_alloc_sites = 0;

  // iterate over all nodes
  for (auto &n: nodes) {

    unsigned num_alloc_sites = std::distance(n.getNode()->begin(), n.getNode()->end());
    if (num_alloc_sites == 0) {
      
      // errs () << "Node without allocation site: ";
      // n.getNode()->write(errs());
      // errs () << "\n";

      num_orphan_nodes++;
      num_orphan_checks += n.getAccesses();
      continue;
    } else {
      max_alloc_sites = std::max (max_alloc_sites, num_alloc_sites);
    }

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

  o << "\t" << alloc_map.size()  << " number of allocation sites\n";
  o << "\t   " << max_alloc_sites  << " max number of allocation sites in a node\n";
  o << "\t" << num_orphan_nodes  << " number of nodes without allocation site\n";
  o << "\t" << num_orphan_checks << " number of memory accesses without allocation site\n";

  if (!DsaInfoDetails) return;
  
  // --- print for each allocation site the set of nodes
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
  
  // --- print for each node its set of allocation sites
  for (auto &n: nodes) {
      o << "  [Node Id " << n.getId () << " Allocation sites Ids {";
      for (const llvm::Value*v : boost::make_iterator_range(n.getNode()->begin(),
                                                            n.getNode()->end())) {
        o << alloc_map[v].first << " ";
      }
      o << "}]\n"; 
  }
}

bool Info::runOnModule (Module &M) {

  m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
  m_tli = &getAnalysis<TargetLibraryInfo> ();
  m_g = &getAnalysis<Global>().getGraph();
 
  // -- Assign a unique (deterministic) id to each node
  //    FIXME: [ m_g->begin()...m_g->end() ) can change from one
  //    execution to another
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
X ("new-dsa-info", "Collect stats and information for dsa clients");
