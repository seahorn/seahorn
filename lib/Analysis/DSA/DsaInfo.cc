#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Analysis/DSA/Info.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/BottomUp.hh"
#include "seahorn/Analysis/DSA/Graph.hh"

#include "avy/AvyDebug.h"

using namespace seahorn::dsa;
using namespace llvm;

// enum DsaKind { GLOBAL, CS_GLOBAL};
// llvm::cl::opt<DsaKind>
// DsaVariant("dsa-variant",
//            llvm::cl::desc ("Choose the dsa variant"),
//            llvm::cl::values 
//            (clEnumValN (GLOBAL   , "global"   , "Context insensitive dsa analysis"),
//             clEnumValN (CS_GLOBAL, "cs-global", "Context sensitive dsa analysis"),
//             clEnumValEnd),
//            llvm::cl::init (GLOBAL));

static bool isStaticallyKnown (const DataLayout* dl, 
                               const TargetLibraryInfo* tli,
                               const Value* v) 
{
  uint64_t size;
  if (getObjectSize (v, size, dl, tli, true)) return (size > 0);
  return false; 
}
      
// return null if there is no graph for f
Graph* InfoAnalysis::getGraph(const Function&f) const
{
  Graph *g = nullptr;
  if (m_dsa.hasGraph(f)) g = &m_dsa.getGraph(f);
  return g;
}

bool InfoAnalysis::is_alive_node::operator()(const NodeInfo& n) 
{
  return n.getNode()->isRead() || n.getNode()->isModified();
}

void InfoAnalysis::addMemoryAccess (const Value* v, Graph& g) 
{
  v = v->stripPointerCasts();
  if (!g.hasCell(*v)) {
    // sanity check
    if (v->getType()->isPointerTy())
      errs () << "DsaInfo: pointer value " << *v << " has not cell\n";
    return;
  }
  
  const Cell &c = g.getCell (*v);
  Node *n = c.getNode();
  auto it = m_nodes_map.find (n);
  if (it != m_nodes_map.end () && !isStaticallyKnown (&m_dl, &m_tli, v))
    ++(it->second);

}        

void InfoAnalysis::countMemoryAccesses (Function&F) 
{
  // A node can be read or modified even if there is no a memory
  // load/store for it. This can happen after nodes are unified.
  // 
  // Here we just count the number of **non-trivial** memory accesses
  // because it is useful for passes that will instrument them.
  auto g = getGraph(F);
  if (!g) return;

  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
    const Instruction *I = &*i;
    if (const LoadInst *LI = dyn_cast<LoadInst>(I)) {
      addMemoryAccess (LI->getPointerOperand (), *g);
    } else if (const StoreInst *SI = dyn_cast<StoreInst>(I)) {
      addMemoryAccess (SI->getPointerOperand (), *g);
    } else if (const MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
      addMemoryAccess (MTI->getDest (), *g);
      addMemoryAccess (MTI->getSource (), *g);
    } else if (const MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
      addMemoryAccess (MSI->getDest (), *g);
    }
  }
}
      
void InfoAnalysis::
printMemoryAccesses (live_nodes_const_range nodes, llvm::raw_ostream &o) const 
{
  // Here counters
  unsigned int total_accesses = 0; // count the number of total memory accesses


  o << " --- Memory access information\n";
  for (auto const &n: nodes) { total_accesses += n.getAccesses(); }
  
  o << "\t" << std::distance(nodes.begin(), nodes.end())  
    << " number of read and modified nodes.\n"
    << "\t" << total_accesses 
    << " number of non-trivial memory accesess"
    << " (load/store/memcpy/memset/memmove).\n";     
  
  //  --- Print a summary of accesses
  std::vector<NodeInfo> sorted_nodes (nodes.begin(), nodes.end());
  unsigned int summ_size = 5;
  o << "\t Summary of the " << summ_size  << " nodes with more accesses:\n";
  std::sort (sorted_nodes.begin (), sorted_nodes.end (),
             [](const NodeInfo &n1, const NodeInfo &n2)
             { return (n1.getAccesses() > n2.getAccesses());});
               
  if (total_accesses > 0) {
    for (auto &n: sorted_nodes) {
      if (summ_size <= 0) break;
      summ_size--;
      if (n.getAccesses() == 0) break;
      o << "\t  [Node Id " << n.getId()  << "] " 
        << n.getAccesses() << " (" 
        << (int) (n.getAccesses() * 100 / total_accesses) 
        << "%) of total memory accesses\n" ;
    }
  }
}

void InfoAnalysis::
printMemoryTypes (live_nodes_const_range nodes, llvm::raw_ostream& o) const
{
  // Here counters
  unsigned num_collapses = 0;    // number of collapsed nodes
  unsigned num_typed_nodes = 0;  // number of typed nodes


  o << " --- Type information\n";
  for (auto &n: nodes) {
    num_collapses += n.getNode()->isCollapsed ();
    num_typed_nodes += (std::distance(n.getNode()->types().begin(),
                                      n.getNode()->types().end()) > 0);
  }
  o << "\t" << num_typed_nodes << " number of typed nodes.\n";
  o << "\t" << num_collapses << " number of collapsed nodes.\n";

  // TODO: print all node's types
}

void InfoAnalysis::
printMemoryAllocSites (live_nodes_const_range nodes, llvm::raw_ostream& o) const
{
  // Here counters
  
  /// number of nodes without allocation sites
  unsigned num_orphan_nodes = 0;
  /// number of checks belonging to orphan nodes.
  unsigned num_orphan_checks = 0;
  /// keep track of maximum number of allocation sites in a single node
  unsigned max_alloc_sites = 0;
  /// number of different types of a node's allocation sites
  unsigned num_non_singleton = 0;


  o << " --- Allocation site information\n";
  // Assign a unique (deterministic) id to each allocation site
  unsigned id = 0;
  // map each allocation site to a set of nodes
  typedef boost::container::flat_set<NodeInfo> NodeInfoSet;
  DenseMap<const llvm::Value*, std::pair<unsigned, NodeInfoSet> > alloc_map;

  // iterate over all nodes
  for (auto &n: nodes) {
    unsigned num_alloc_sites = std::distance(n.getNode()->begin(), n.getNode()->end());
    if (num_alloc_sites == 0) {
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

  LOG ("dsa-info-alloc-sites",
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
       });
  
  // --- print for each node its set of allocation sites
  for (auto &n: nodes) 
  {
    // o << "  [Node Id " << n.getId () << " Allocation sites Ids {";
    SmallPtrSet<Type*,32> allocTypes;
    for (const llvm::Value*v : 
         boost::make_iterator_range(n.getNode()->begin(), n.getNode()->end())) 
    {
      allocTypes.insert(v->getType());
      //o << alloc_map[v].first << " ";
    }
    // o << "}]\n";

    num_non_singleton += (allocTypes.size() > 1);

    LOG ("dsa-info-alloc-types",
         if (allocTypes.size () > 1) {
           n.getNode()->write(o);
           o << "\nTypes of the node's allocation sites\n";
           for (auto ty : allocTypes) { 
             o << "\t" << *ty << "\n";
           }
         });
  }

  o << "\t" << num_non_singleton << " allocation sites with more than one type\n";
}

bool InfoAnalysis::runOnModule (Module &M) 
{
  for (auto &f: M) { runOnFunction (f); }
    
  errs () << " ========== Begin Dsa info  ==========\n";

  printMemoryAccesses (live_nodes (), llvm::errs());
  printMemoryTypes (live_nodes (), llvm::errs());
  printMemoryAllocSites (live_nodes (), llvm::errs());
  
  errs () << " ========== End Dsa info  ==========\n";

  return false;
}

bool InfoAnalysis::runOnFunction (Function &f) 
{  
  auto g = getGraph(f);
  if (!g) return false;

  // -- Assign a unique (deterministic) id to each node
  //    FIXME: [ g->begin()...g->end() ) can change from one
  //    execution to another
  for (auto const& n: boost::make_iterator_range(g->begin(), g->end()))
    m_nodes_map.insert(std::make_pair(&n, NodeInfo(&n, m_nodes_map.size()+1)));
 
  // compute here stuff that it's not computed by Dsa
  countMemoryAccesses(f);

  return false;
}


/// LLVM pass

void InfoPass::getAnalysisUsage (AnalysisUsage &AU) const 
{
  AU.addRequired<DataLayoutPass> ();
  AU.addRequired<TargetLibraryInfo> ();
  //AU.addRequired<ContextInsensitiveGlobal> ();
  AU.addRequired<ContextSensitiveGlobal> ();
  AU.setPreservesAll ();
}

bool InfoPass::runOnModule (Module &M) 
{

  auto dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
  auto tli = &getAnalysis<TargetLibraryInfo> ();
  //auto dsa = &getAnalysis<ContextInsensitiveGlobal>().getGlobalAnalysis();
  auto dsa = &getAnalysis<ContextSensitiveGlobal>().getGlobalAnalysis();

  m_ia.reset (new InfoAnalysis (*dl, *tli, *dsa));
  return m_ia->runOnModule (M);
  return false;
}


char InfoPass::ID = 0;

static llvm::RegisterPass<InfoPass> 
X ("dsa-info", "Collect stats and information for dsa clients");
