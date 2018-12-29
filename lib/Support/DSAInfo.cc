#include "seahorn/Support/DSAInfo.hh"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"

/*

 - A DS node is a memory object identified by the DSA analysis.

 - A program variable of pointer type can be mapped to a DS node plus
   an offset.

 - An allocation site is either a global variable, alloca instruction
   or malloc-like function. Allocation sites creates memory objects. 

 - An identified DS node might not have an allocation site if the
   allocation site is defined in an external function.

 This analysis pass provides the following functionality:

 - Identify all DS nodes and the number of read (load) and write
   (store) accesses to each one, and assign deterministically a
   numeric identifier to each DS node. These identifiers are useful
   for other passes (such as abc)

 - Identify allocation sites and assign deterministically a numeric
   identifier to each one.

 - For each allocation site identify its DS node(s). Ideally, we
   should have one DS node per allocation site.

*/

static llvm::cl::opt<bool>
DSAInfoToOutput("llvm-dsa-stats",
    llvm::cl::desc ("Llvm DSA: print DSA statistics"),
    llvm::cl::init (false));

static llvm::cl::opt<bool>
DSAInfoToOutputVerbose("dsa-info-verbose",
    llvm::cl::desc ("Llvm DSA: print verbose information about DSA"),
    llvm::cl::init (false),
    llvm::cl::Hidden);

static llvm::cl::opt<std::string>
DSAInfoToFile("dsa-info-to-file",
    llvm::cl::desc ("Llvm DSA: write all allocation sites to a file"),
    llvm::cl::init (""),
    llvm::cl::Hidden);

#ifdef HAVE_DSA
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"

#include "boost/range.hpp"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn
{
  using namespace llvm;

  static bool IsStaticallyKnown (const DataLayout* dl, 
                                 const TargetLibraryInfo* tli,
                                 const Value* V) {
    uint64_t Size;
    if (getObjectSize (V, Size, *dl, tli))
      return (Size > 0);
    
    return false; 
  }

  void DSAInfo::addNode (const DSNode* n) {
    auto it = m_nodes.find (n);
    if (it == m_nodes.end ()) {
      auto wn = WrapperDSNode (n);
      m_nodes.insert (std::make_pair(n, wn));
    }
  }

  void DSAInfo::insertReferrersMap (const DSNode* n, const Value* v) {
   auto it = m_referrers_map.find (n);
   if (it != m_referrers_map.end ())
        it->second.insert (v);
   else {
     ValueSet s;
     s.insert (v);
     m_referrers_map.insert (std::make_pair (n, s));
   }
 }

  bool DSAInfo::hasReferrers (const DSNode* n) const {
    return m_referrers_map.find (n) != m_referrers_map.end ();
  }

  const DSAInfo::ValueSet& DSAInfo::getReferrers (const DSNode* n) const {
    auto it = m_referrers_map.find (n);
    assert (hasReferrers (n));
    return it->second;
  }

  bool DSAInfo::addAllocSite (const Value* v, unsigned int & site_id) {
    typedef boost::bimap<const Value*, unsigned int>::value_type bm_type;
    
    site_id = 0;
     auto it = m_alloc_sites.left.find (v);
     if (it == m_alloc_sites.left.end ()) {
       site_id = m_alloc_sites.size () + 1;
       m_alloc_sites.insert (bm_type (v, site_id));
       return true;
     } else {
       site_id = it->second;
       return false;
     }
  }

   
  void DSAInfo::countAccesses (const DataLayout* dl, const TargetLibraryInfo* tli,
                               DSGraph* dsg, Value* V) {    
                               
    const DSNode* n = dsg->getNodeForValue (V).getNode ();
    if (!n) n = m_gDsg->getNodeForValue (V).getNode ();
    if (!n) return;

    auto It = m_nodes.find (n);
    if (It != m_nodes.end () && !IsStaticallyKnown (dl, tli, V))
      It->second.m_accesses++;
  }        

  DSAInfo::DSAInfo () : 
      llvm::ModulePass (ID), 
      m_dsa (nullptr), m_gDsg (nullptr) { }

    
  unsigned int DSAInfo::getDSNodeID (const DSNode* n) const {
     auto it = m_nodes.find (n);
     assert (it != m_nodes.end ());
     return it->second.m_id;
  }

  bool DSAInfo::isAccessed (const DSNode* n) const {
     auto it = m_nodes.find (n);
     assert (it != m_nodes.end ());
     return it->second.m_accesses > 0;
  }

  const unsigned int DSAInfo::getAllocSiteID (const Value* V) const {
    auto it = m_alloc_sites.left.find (V);
    if (it != m_alloc_sites.left.end ())
      return it->second;
    else
      return 0; // not found
  }

  const Value* DSAInfo::getAllocValue (unsigned int alloc_site_id) const {
    auto it = m_alloc_sites.right.find (alloc_site_id);
    if (it != m_alloc_sites.right.end ())
      return it->second;
    else
      return nullptr; //not found
  }

  void DSAInfo::releaseMemory () {
    m_nodes.clear();
    m_referrers_map.clear();
    m_alloc_sites.clear();
  }

  // Print information about DSA analysis
  void DSAInfo::writeDSAnalysisInfo (llvm::raw_ostream& o) {
    
      std::vector<WrapperDSNode> nodes_vector;
      nodes_vector.reserve (m_nodes.size ());
      for (auto &kv: m_nodes) { 
        if (kv.second.m_accesses > 0)
          nodes_vector.push_back (kv.second); 
      }
      o << " --- Memory access information\n";

      //o << m_nodes.size () << " Total number of DS nodes.\n";      
      // -- Some DSNodes are never read or written because after they
      //    are created they are only passed to external calls.
      o << " " << nodes_vector.size ()  
        << " Total number of accessed (read/written) DS nodes.\n";     
      unsigned int total_collapsed = 0;
      for (auto &n: nodes_vector) 
	total_collapsed += n.m_n->isNodeCompletelyFolded();

      o << " " << total_collapsed << " Total number of collapsed DS nodes.\n";     

      unsigned int total_accesses = 0;
      for (auto &n: nodes_vector) 
        total_accesses += n.m_accesses;

      o << " " << total_accesses << " Total number of memory accesses.\n";     

      {  //  Print a summary of accesses
        unsigned int sum_size = 5;
        o << " Summary of the " << sum_size  << " most accessed DS nodes:\n";
        std::vector<WrapperDSNode> tmp_nodes_vector (nodes_vector);
        std::sort (tmp_nodes_vector.begin (), tmp_nodes_vector.end (),
                   [](WrapperDSNode n1, WrapperDSNode n2){
                     return (n1.m_accesses > n2.m_accesses);
                   });
        if (total_accesses > 0) {
          for (auto &n: tmp_nodes_vector) {
          if (sum_size <= 0) break;
          sum_size--;
          if (n.m_accesses == 0) break;
          o << "   [Node Id " << n.m_id  << "] " 
            << (int) (n.m_accesses * 100 / total_accesses) 
            << "% of total memory accesses\n" ;
          }
          o << "   ...\n";
        }
      }

      if (DSAInfoToOutputVerbose) 
      {
        o << "Detailed information about all DS nodes\n";
        std::sort (nodes_vector.begin (), nodes_vector.end (),
                   [](WrapperDSNode n1, WrapperDSNode n2){
                     return (n1.m_id < n2.m_id);
                   });
        
        for (auto &n: nodes_vector) {
          if (!hasReferrers (n.m_n)) continue;
          const ValueSet& referrers = getReferrers (n.m_n);
          o << "  [Node Id " << n.m_id  << "] ";
          
          if (n.m_rep_name != "") {
            if (n.m_n->getUniqueScalar ()) {
              o << " singleton={" << n.m_rep_name << "}";
            } else {
              o << " non-singleton={" << n.m_rep_name << ",...}";
            }
          }
          o << "  with " << n.m_accesses << " memory accesses \n";
          
          // --- print type information
          DSNode * nn = const_cast<DSNode*> (n.m_n);
          LOG("dsa-info", errs () << "     ";  nn->dump ());
          if (nn->isNodeCompletelyFolded())  {
            o << "  Types={collapsed";
          } else if (nn->hasNoType ())
            o << "  Types={void";
          else {
            o << "  Types={";
            DSNode::type_iterator ii = nn->type_begin(), ie = nn->type_end();
            DSNode::type_iterator jj = ii;
            if (++jj == ie) {
              auto ty_set_ptr = ii->second;
              if (ty_set_ptr->size () == 1) {
                o << **(ty_set_ptr->begin ());
              } else {
                svset<Type*>::const_iterator ki = (*ty_set_ptr).begin (), ke = (*ty_set_ptr).end ();
                o << "[";
                for (; ki != ke; ) { 
                  o << **ki;
                  ++ki;
                  if (ki != ke) o << " | ";
                }
                o << "]";
              }
            }
            else {
              o << "struct {";
              while (ii != ie) {
                o << ii->first << ":";
                if (!ii->second) { 
                  o << "void";
                } else {
                  auto ty_set_ptr = ii->second;
                  if (ty_set_ptr->size () == 1) {
                    o << **(ty_set_ptr->begin ());
                  } else {
                    svset<Type*>::const_iterator ki = ty_set_ptr->begin (), ke = ty_set_ptr->end ();
                    o << "[";
                    for (; ki != ke; ) { 
                      o << **ki;
                      ++ki;
                      if (ki != ke) o << " | ";
                    }
                    o << "]";
                  }
                }
                ++ii;
                if (ii != ie)
                  o << ",";   
              }
              o << "}*";
            }
          }
          // --- print llvm values referring to the DSNodes
          o << "}\n";

          LOG("dsa-info", 
              o << "  " << std::distance(referrers.begin(), referrers.end()) 
              << " Referrers={\n";
              for (auto const& r : referrers) {
                if (r->hasName ()) o << "    " << r->getName ();
                else o << "  " << *r;  
                o << "\n";
              }
              o << "  }\n");
        }
      }
  }        

  void DSAInfo::findDSNodeForValue (const Value* v, std::set<unsigned int>& nodes) {
    for (auto &kv: m_referrers_map) {
      const ValueSet& referrers = kv.second;
      if (referrers.count (v) > 0)
        if (getDSNodeID (kv.first) > 0)
          nodes.insert( getDSNodeID (kv.first));
    }
  }

  // Print information about all alllocation sites
  void DSAInfo::writeAllocSitesInfo (llvm::raw_ostream& o, bool isFile) {
    if (!isFile && DSAInfoToOutput)
      o << " --- Allocation site information\n";

    // -- total number of allocations in the program
    // o << m_alloc_sites.right.size ()  
    //   << " Total number of allocation sites.\n";     

    unsigned actual_alloc_sites = 0;
    for (auto p: m_alloc_sites.right) {
      std::set<unsigned int> nodes;
      findDSNodeForValue (p.second, nodes);
      if (nodes.empty ()) continue;
      actual_alloc_sites++;
    }      

    // -- total number of allocations that belong to a DSNode that is
    //    ever read or written. Some DSNodes are never read or written
    //    because after they are created they are only passed to
    //    external calls.
    if (!isFile && DSAInfoToOutput) {
      o << " " << actual_alloc_sites << " allocation sites.\n";     
    }
    
    //if (!DSAInfoToOutputVerbose && !isFile) return;

    std::set <unsigned int> seen;
    for (auto p: m_alloc_sites.right) {
      std::set<unsigned int> nodes;
      findDSNodeForValue (p.second, nodes);
      // if not DSNode found then the alloca belongs to a DSNode to
      // which nobody reads/write from/to.
      if (nodes.empty ()) continue;

      // -- Sanity check: an alloca site belongs only to one DSNode
      if (nodes.size () > 1) {
        if (!isFile && DSAInfoToOutput) {
          o << "DSAInfo found an allocation site " << p.first 
            << " associated with multiple DSNodes {";
          for (auto NodeId: nodes) o << NodeId << ","; 
          o << "}\n";
        }
        continue;
      }

      if (isFile) {
        o << p.first << "," << *(nodes.begin ()) << "\n";
      } 
      else if (DSAInfoToOutputVerbose){
        o << "  [Alloc site Id " << p.first << " DSNode Id " << *(nodes.begin ()) << "]"
          << "  " << *p.second  << "\n";
      }
      seen.insert (*(nodes.begin ()));
    }

    // -- Sanity check: each DSNode has an allocation site

    // Number of accesses that have an allocation site
    unsigned num_accesses_without_alloc_site = 0;
    unsigned num_nodes_without_alloc_site = 0;
    for (auto& kv: m_nodes) {
      unsigned int NodeID = kv.second.m_id;
      if (seen.count (NodeID) > 0) continue;
      // An ID can be 0 (undefined) if the node did not have any
      // access
      if (NodeID > 0) {
        if (isFile) {
          o << "," << NodeID << "\n";
        } else {
          if (DSAInfoToOutputVerbose)
            errs () << "DSAInfo cannot find allocation site for DSNode ID=" << NodeID << "\n";
          num_nodes_without_alloc_site ++;
          num_accesses_without_alloc_site += kv.second.m_accesses;
          LOG ("dsa-info", 
               const ValueSet& referrers = getReferrers (kv.second.m_n);
               for (auto const& r : referrers) {
                 if (r->hasName ())
                   o << "\t  " << r->getName ();
                 else 
                   o << "\t" << *r; 
               o << "\n";
               });
        }
      }
    }
    if (DSAInfoToOutput)
    {
      errs () << " " << num_nodes_without_alloc_site 
              << " nodes without allocation site.\n";
      errs () << " " << num_accesses_without_alloc_site 
              << " memory accesses without allocation site.\n";
    }
  }

  bool DSAInfo::runOnModule (llvm::Module &M) {  


      m_dsa = &getAnalysis<SteensgaardDataStructures> ();
      m_gDsg = m_dsa->getGlobalsGraph ();

      if (DSAInfoToOutput)
        llvm::errs () << " ========== Begin Llvm Dsa info ==========\n";

      // Collect all referrers per DSNode
      DSScalarMap &SM = m_gDsg->getScalarMap ();
      for (const Value*v : boost::make_iterator_range (SM.global_begin (), 
                                                       SM.global_end ())){
        const DSNodeHandle lN = SM[v];
        if (lN.isForwarding ()) continue;

        if (const DSNode* n = lN.getNode ()) {
          addNode (n);
          insertReferrersMap  (n, v);
        }
      }

      for (auto &F: M) { 
        if (F.isDeclaration ()) continue;

        DSGraph* dsg = m_dsa->getDSGraph (F);
        if (!dsg) continue;

        DSScalarMap &SM = dsg->getScalarMap ();
        for (auto const &kv : boost::make_iterator_range (SM.begin (), 
                                                          SM.end ())){
          const Value* v = kv.first;
          DSNodeHandle lN = kv.second;
          if (lN.isForwarding ()) continue;

          if (const DSNode* n = lN.getNode ()) {
            addNode (n);
            insertReferrersMap  (n, v);
          }
        }     
      }

      const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
      const DataLayout* dl = &M.getDataLayout ();

      // Count number of reads and writes to each DSNode
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;

        DSGraph* dsg = m_dsa->getDSGraph (F);
        if (!dsg) continue;
        DSGraph* gDsg = dsg->getGlobalsGraph (); 
             
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
          Instruction *I = &*i;
          if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
            countAccesses (dl, tli, dsg, LI->getPointerOperand ());
          } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
            countAccesses (dl, tli, dsg, SI->getPointerOperand ());
          } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
            countAccesses (dl, tli, dsg, MTI->getDest ());
            countAccesses (dl, tli, dsg, MTI->getSource ());
          } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
            countAccesses (dl, tli, dsg, MSI->getDest ());
          }   
        }
      }

      // figure out deterministically a representative name for each DSNode
      for (auto &kv: m_nodes) {
        WrapperDSNode& n = kv.second;
        if (!hasReferrers (n.m_n) || n.m_accesses == 0) continue;

        // we collect all referrers and sort by their names in order
        // to make sure that the representative is always
        // chosen deterministically.
        const ValueSet& referrers = getReferrers (n.m_n);
        std::vector<std::string> named_referrers;
        named_referrers.reserve (referrers.size ());
        for (auto &r: referrers) {
          if (r->hasName ()) {
            named_referrers.push_back (r->getName().str());
          } 
        }

        // if no named value we create a name from the unnamed values.
        if (named_referrers.empty ()) {
          std::string str("");
          raw_string_ostream str_os (str);
          for (auto &r: referrers) {
            if (!r->hasName ()) {
              // build a name from the unnamed value
              r->print (str_os); 
              std::string inst_name (str_os.str ());
              named_referrers.push_back (inst_name);
            }
          }
        }

        std::sort (named_referrers.begin (), named_referrers.end (),
                   [](std::string s1, std::string s2){
                     return (s1 < s2);
                   });

        if (!named_referrers.empty ()) // should not be empty
          n.m_rep_name = named_referrers [0];
        
      }

      // Try to assign deterministically a numeric id to each node
      std::vector<WrapperDSNode*> nodes_vector;
      nodes_vector.reserve (m_nodes.size ());
      for (auto &kv: m_nodes) { 
        if (kv.second.m_accesses > 0)
          nodes_vector.push_back (&(kv.second)); 
      }
      std::sort (nodes_vector.begin (), nodes_vector.end (),
                 [](WrapperDSNode* n1, WrapperDSNode* n2){
                   return ((n1->m_rep_name < n2->m_rep_name) ||
                           ((n1->m_rep_name == n2->m_rep_name) &&
                            (n1->m_accesses < n2->m_accesses)));
                 });
      unsigned id = 1;
      for (auto n: nodes_vector) n->m_id = id++;

      // Identify allocation sites and assign a numeric id to each one
      for (auto &GV: M.globals ()) {
        Type *Ty = cast<PointerType>(GV.getType())->getElementType();
        if (!Ty->isSized()) {
          if (DSAInfoToOutput)
            errs () << "DSAInfo ignored unsized " << GV << " as allocation site\n";
          continue;
        }
        if (!GV.hasInitializer()) {
          if (DSAInfoToOutput)
            errs () << "DSAInfo ignored uninitialized " << GV << " as allocation site\n";
          continue;
        }
        if (GV.hasSection()) {
          StringRef Section(GV.getSection());
          // Globals from llvm.metadata aren't emitted, do not instrument them.
          if (Section == "llvm.metadata") continue;
        }
        unsigned int alloc_site_id; 
        addAllocSite (&GV, alloc_site_id);
      }
      
      for (auto &F: M) {
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {      
          Instruction* I = &*i;
          if (AllocaInst* AI = dyn_cast<AllocaInst> (I)) {
            Type *Ty = AI->getAllocatedType();
            if (!Ty->isSized() || dl->getTypeAllocSize(Ty) <= 0) {
              if (DSAInfoToOutput)
                errs () << "DSAInfo ignored unsized " << *AI << " as allocation site\n";
              continue;
            }
            unsigned int alloc_site_id; 
            addAllocSite (AI, alloc_site_id);
          } else if (isAllocationFn (I, tli, true)) {
            Value *V = I;
            V = V->stripPointerCasts();
            unsigned int alloc_site_id; 
            addAllocSite (V, alloc_site_id);
          }
        }
      }


      if (DSAInfoToOutput)
        writeDSAnalysisInfo(errs ());
      writeAllocSitesInfo(errs (), false);
      if (DSAInfoToFile != "") {
        std::string filename(DSAInfoToFile);
        std::error_code EC;
        raw_fd_ostream File(filename, EC, sys::fs::F_Text);
        File << "alloc_site,ds_node\n";
        writeAllocSitesInfo(File, true);
        File.close();
      }

      if (DSAInfoToOutput)
        llvm::errs () << " ========== End Llvm Dsa info ==========\n";

      return false;
  }

  void DSAInfo::getAnalysisUsage (llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
    AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
  }

} // end namespace
#endif

namespace seahorn{
 
  char DSAInfo::ID = 0;

  llvm::Pass* createDSAInfoPass () { return new DSAInfo (); }

  static llvm::RegisterPass<DSAInfo> 
  X ("dsa-info", "Show information about DSA Nodes");

} 
