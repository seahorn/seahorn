#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Analysis/DSA/Info.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Graph.hh"

#include "ufo/Stats.hh"

#include "avy/AvyDebug.h"

using namespace seahorn::dsa;
using namespace llvm;

static llvm::cl::opt<std::string>
DsaInfoToFile("sea-dsa-info-to-file",
    llvm::cl::desc ("Dump some Dsa info into a file"),
    llvm::cl::init (""),
    llvm::cl::Hidden);

static bool isStaticallyKnown (const DataLayout* dl, 
                               const TargetLibraryInfo* tli,
                               const Value* v) 
{
  uint64_t size;
  if (getObjectSize (v, size, dl, tli, true)) return (size > 0);
  return false; 
}
      
// return null if there is no graph for f
Graph* InfoAnalysis::getDsaGraph(const Function&f) const
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
      errs () << "WARNING DsaInfo: pointer value " << *v << " has not cell\n";
    return;
  }
  
  const Cell &c = g.getCell (*v);
  Node *n = c.getNode();
  auto it = m_nodes_map.find (n);
  if (it != m_nodes_map.end () && !isStaticallyKnown (&m_dl, &m_tli, v))
    ++(it->second);

}        

void InfoAnalysis::countMemoryAccesses (const Function&F) 
{
  // A node can be read or modified even if there is no a memory
  // load/store for it. This can happen after nodes are unified.
  // 
  // Here we just count the number of **non-trivial** memory accesses
  // because it is useful for passes that will instrument them.
  auto g = getDsaGraph(F);
  if (!g) return;

  for (const_inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  
  {
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
  
  ufo::Stats::uset ("DsaNumOfNodes", std::distance (nodes.begin () , nodes.end ()));

  o << "\t" << std::distance(nodes.begin(), nodes.end())  
    << " number of read or modified nodes.\n"
    << "\t" << total_accesses 
    << " number of non-trivial memory accesses"
    << " (load/store/memcpy/memset/memmove).\n";     
  
  //  --- Print a summary of accesses
  std::vector<NodeInfo> sorted_nodes (nodes.begin(), nodes.end());
  unsigned int summ_size = 5;
  o << "\t Summary of the " << summ_size  << " nodes with more accesses:\n";
  std::sort (sorted_nodes.begin (), sorted_nodes.end (),
             [](const NodeInfo &n1, const NodeInfo &n2)
             { return (n1.getAccesses() > n2.getAccesses());});
               
  if (total_accesses > 0) {
    for (const auto &n: sorted_nodes) {
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
  for (const auto &n: nodes) {
    num_collapses += n.getNode()->isCollapsed ();
    num_typed_nodes += (std::distance(n.getNode()->types().begin(),
                                      n.getNode()->types().end()) > 0);
  }
  o << "\t" << num_typed_nodes << " number of typed nodes.\n";
  o << "\t" << num_collapses << " number of collapsed nodes.\n";

  ufo::Stats::uset ("DsaNumOfCollapsedNodes", num_collapses);

  // TODO: print all node's types
}
template <typename BiMap>
inline bool AddAllocSite (const Value* v, unsigned int &site_id, BiMap& alloc_sites_bimap) 
{
  auto it = alloc_sites_bimap.left.find (v);
  if (it == alloc_sites_bimap.left.end ()) 
  {
    site_id = alloc_sites_bimap.size () + 1;
    alloc_sites_bimap.insert (typename BiMap::value_type (v, site_id));
    return true;
  } 
  else 
  {
    site_id = it->second;
    return false;
  }
}

bool compareValues (const Value* v1, const Value* v2)
{
  assert (v1->hasName());
  assert (v2->hasName());
  return (v1->getName () < v2->getName ());
}

void InfoAnalysis::assignAllocSiteIdAndPrinting 
(live_nodes_const_range nodes, llvm::raw_ostream& o, std::string outFile) 
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
  
  // pretty-printer: map each allocation site to a set of nodes
  DenseMap<const llvm::Value*, std::pair<unsigned, NodeInfoSet> > alloc_printing_map;

  /// XXX: sort nodes by id's to achieve determinism across different
  /// executions.
  std::vector<NodeInfo> nodes_sorted;
  for (auto n: nodes) { nodes_sorted.push_back (n);} 
  std::sort (nodes_sorted.begin(), nodes_sorted.end());
  // iterate over all nodes
  for (const auto &n: nodes_sorted) 
  {
    unsigned num_alloc_sites = n.getNode()->getAllocSites ().size ();
    if (num_alloc_sites == 0) 
    {
      o << *n.getNode () << " has no alllocation site\n";
      num_orphan_nodes++;
      num_orphan_checks += n.getAccesses();
      continue;
    } 
    else 
      max_alloc_sites = std::max (max_alloc_sites, num_alloc_sites);

    /// XXX: sort alloca sites by name to achieve determinism across
    /// different executions.
    
    // iterate over all allocation sites
    auto &n_alloca_sites = n.getNode ()->getAllocSites ();
    std::vector<const llvm::Value*> n_alloca_sites_sorted (n_alloca_sites.begin(),
							   n_alloca_sites.end());
    std::sort (n_alloca_sites_sorted.begin(),
	       n_alloca_sites_sorted.end(), compareValues);
    for (const llvm::Value*v : n_alloca_sites_sorted) 
    {
      // assign a unique id to the allocation site for Dsa clients
      unsigned int site_id;
      AddAllocSite (v, site_id, m_alloc_sites);

      // for pretty printer
      auto it = alloc_printing_map.find (v);
      if (it != alloc_printing_map.end())
        it->second.second.insert(n);
      else 
      {
        NodeInfoSet s;
        s.insert(n);
        alloc_printing_map.insert(std::make_pair(v, 
                                                 std::make_pair(site_id, s)));
      }
    }
  }

  o << "\t" << alloc_printing_map.size()  << " number of allocation sites\n";
  o << "\t   " << max_alloc_sites  << " max number of allocation sites in a node\n";
  o << "\t" << num_orphan_nodes  << " number of nodes without allocation site\n";
  o << "\t" << num_orphan_checks << " number of memory accesses without allocation site\n";

  ufo::Stats::uset ("DsaNumOfAllocationSites", alloc_printing_map.size());

  if (outFile != "")
  {
    std::string filename (outFile);
    std::error_code EC;
    raw_fd_ostream file (filename, EC, sys::fs::F_Text);
    file << "alloc_site,ds_node\n";
    for (auto &kv: alloc_printing_map) 
    {
      for (const auto &nodeInfo: kv.second.second)
        file <<  kv.second.first << "," << nodeInfo.getId () << "\n";
    }
    file.close();
  }

  // --- print for each allocation site the set of nodes

  LOG ("dsa-info-alloc-sites",
       for (auto &kv: alloc_printing_map) {
         o << "\t  [Alloc site Id " << kv.second.first << " DSNode Ids {";
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
  for (const auto &n: nodes) 
  {
    SmallPtrSet<Type*,32> allocTypes;
    for (const llvm::Value*v : n.getNode ()->getAllocSites ()) 
      allocTypes.insert(v->getType());

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

template <typename PairRange, typename SetMap>
inline void InsertReferrer (PairRange r, SetMap &m) 
{
  for (auto &kv: r)
  {
    const Node *n = kv.second->getNode ();
    if (!(n->isRead () || n->isModified ())) continue;
    
    auto it = m.find (n);
    if (it != m.end ())
      it->second.insert (kv.first);
    else
    {
      typename SetMap::mapped_type s;
      s.insert (kv.first);
      m.insert(std::make_pair (n, s));
    }
  }
}

// Assign a unique name to a value for the whole module
std::string InfoAnalysis::getName (const Function&fn, const Value& v) 
{
  assert (v.hasName ());
  const Value * V = v.stripPointerCasts();
  
  auto it = m_names.find (V);
  if (it != m_names.end ()) return it->second;

  std::string name = fn.getName ().str() + "." + v.getName ().str();
  auto res = m_names.insert (std::make_pair (V, name));
  return res.first->second;

  // if (V->hasName ()) return V->getName().str();
  // auto it = m_names.find (V);
  // if (it != m_names.end ()) return it->second;
  // // FIXME: this can be really slow!
  // // XXX: I don't know a better way to obtain a string-like
  // // representation from a value.
  // std::string str("");
  // raw_string_ostream str_os (str);
  // V->print (str_os); 
  // auto res = m_names.insert (std::make_pair (V, str_os.str ()));
  // return res.first->second;
}


// Assign to each node a **deterministic** id that is preserved across
// different executions
void InfoAnalysis::assignNodeId (const Function& fn, Graph* g)
{
  #if 1
  /// XXX: Assume class Node already assigns a global id to each node

  for (auto &kv: boost::make_iterator_range (g->scalar_begin(), 
                                             g->scalar_end())) 
  {
    const Node *n = kv.second->getNode ();
    m_nodes_map.insert(std::make_pair(n,NodeInfo(n, n->getId(), "")));
  }                                   
                                      
  for (auto &kv: boost::make_iterator_range (g->formal_begin(), 
                                             g->formal_end())) 
  {
    const Node *n = kv.second->getNode ();
    m_nodes_map.insert(std::make_pair(n,NodeInfo(n, n->getId(), "")));
  }                                   

  for (auto &kv: boost::make_iterator_range (g->return_begin(), 
                                             g->return_end())) 
  {
    const Node *n = kv.second->getNode ();
    m_nodes_map.insert(std::make_pair(n,NodeInfo(n, n->getId(), "")));
  }                                   
                                               
  #else
  /// XXX: Try to build a global id from the name of a node's
  /// representative. The representative is chosen deterministically.

  typedef boost::unordered_map<const Node*, ValueSet  > ReferrerMap;
  typedef std::vector<std::pair<const Node*, std::string> > ReferrerRepVector;

  ReferrerMap ref_map;
  ReferrerRepVector sorted_ref_vector;

  // Build referrers for each node
  InsertReferrer (boost::make_iterator_range (g->scalar_begin(), 
                                              g->scalar_end()), ref_map);
  InsertReferrer (boost::make_iterator_range (g->formal_begin(), 
                                              g->formal_end()), ref_map);
  InsertReferrer (boost::make_iterator_range (g->return_begin(), 
                                              g->return_end()), ref_map);

  // Find *deterministically* a representative for each node from its
  // set of referrers
  for (auto &kv: ref_map)
  {
    const Node * n = kv.first;
    const ValueSet& refs = kv.second;

    // Transform addresses to strings 
    // XXX: StringRef does not own the string data so we cannot use here
    std::vector<std::string> named_refs;
    named_refs.reserve (refs.size ());
    for (auto v: refs) 
      if (v->hasName ()) 
      {
        /// XXX: constant expressions won't have names
        named_refs.push_back (getName (fn, *v));
      }
      
    // Sort strings
    std::sort (named_refs.begin (), named_refs.end ());

    // Choose the first one
    if (!named_refs.empty ()) 
      sorted_ref_vector.push_back(std::make_pair(n, named_refs [0]));
    else
      errs () << "WARNING DsaInfo: not found representative for node\n";
  }

  if (sorted_ref_vector.empty()) return;

  // Sort nodes 
  unsigned num_ref = sorted_ref_vector.size ();
  std::sort (sorted_ref_vector.begin (), sorted_ref_vector.end (),
             [](std::pair<const Node*, std::string> p1, 
                std::pair<const Node*, std::string> p2){
               return (p1.second < p2.second);
             });

  if (sorted_ref_vector.size () != num_ref)
    errs () << "WARNING DsaInfo: node representatives should be unique\n";
  
  // -- Finally, assign a unique (deterministic) id to each node
  //    The id 0 is reserved in case some query goes wrong.
  for (auto &kv: sorted_ref_vector)
    m_nodes_map.insert(std::make_pair(kv.first, 
                                      NodeInfo(kv.first, 
                                               m_nodes_map.size()+1,
                                               kv.second)));
  #endif 
}

bool InfoAnalysis::runOnFunction (Function &f) 
{  
  if (Graph* g = getDsaGraph(f))
  {
    LOG ("dsa-info",
         errs () << f.getName () 
                 << " has " << std::distance (g->begin(), g->end()) << " nodes\n");

    // XXX: If the analysis is context-insensitive all functions have
    // the same graph so we just need to compute the id's for the
    // first graph.
    if (m_seen_graphs.count (g) <= 0)
      assignNodeId (f, g); 

    countMemoryAccesses (f);
  }
  return false;
}

bool InfoAnalysis::runOnModule (Module &M) 
{

  unsigned num_of_funcs = 0;
  for (auto &f: M) 
  { 
    runOnFunction (f); 
    if (f.isDeclaration () || f.empty ()) 
      continue;
    num_of_funcs++; 
  }

  ufo::Stats::uset ("NumOfFunctions", num_of_funcs);

  // discards output if verbose mode is disabled
  raw_ostream &o = (m_verbose ? errs () : nulls ());

  o << " ========== Begin Dsa info  ==========\n";

  printMemoryAccesses (live_nodes (), o);
  printMemoryTypes (live_nodes (), o);
  assignAllocSiteIdAndPrinting  (live_nodes (), o, DsaInfoToFile);
  
  o << " ========== End Dsa info  ==========\n";

  return false;
}

// External API for Dsa clients
bool InfoAnalysis::isAccessed (const Node&n) const 
{ 
  auto it = m_nodes_map.find (&n);
  if (it != m_nodes_map.end ())
    return (it->second.getAccesses () > 0);
  else
    return false; // not found
}

unsigned int InfoAnalysis::getDsaNodeId (const Node&n) const 
{ 
  auto it = m_nodes_map.find (&n);
  if (it != m_nodes_map.end ())
    return it->second.getId ();
  else
    return 0; // not found
}

unsigned int InfoAnalysis::getAllocSiteId (const Value* V) const
{ 
  auto it = m_alloc_sites.left.find (V);
  if (it != m_alloc_sites.left.end ())
    return it->second;
  else
    return 0; // not found
}

const Value* InfoAnalysis::getAllocValue (unsigned int alloc_site_id) const
{ 
  auto it = m_alloc_sites.right.find (alloc_site_id);
  if (it != m_alloc_sites.right.end ())
    return it->second;
  else
    return nullptr; //not found
} 

