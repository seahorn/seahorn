#ifndef __DSA_INFO__HH__
#define __DSA_INFO__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

#include "seahorn/config.h"

#include <boost/bimap.hpp>

#ifndef HAVE_DSA
namespace seahorn
{
  using namespace llvm;

  class DSAInfo : public llvm::ModulePass {
   public:
    static char ID;
    DSAInfo () : llvm::ModulePass (ID){ }

    virtual bool runOnModule (llvm::Module &M) { return false;}
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const{ AU.setPreservesAll ();}
    virtual const char* getPassName () const {return "DSAInfo";}
  };
}
#else
// Real implementation starts there
#include "dsa/Steensgaard.hh"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

namespace llvm {
   class DataLayout;
   class TargetLibraryInfo;
}

namespace seahorn
{
  using namespace llvm;
  
  class DSAInfo : public llvm::ModulePass
  {
    typedef std::set <const Value*> ValueSet;

   public:

    struct WrapperDSNode {
      const DSNode* m_n;
      unsigned m_id;
      std::string m_rep_name;
      unsigned m_accesses;

      WrapperDSNode (const DSNode* n)
          : m_n (n), m_id (0), m_accesses (0) { }

      // use m_n for ordering 
      bool operator<(const WrapperDSNode& o) const 
      { return m_n < o.m_n; }

      bool operator==(const WrapperDSNode& o) const 
      { return m_n == o.m_n; }

      // unsigned numOfTypes () const {
      //   return std::distance (m_n->type_begin (), m_n->type_end ());
      // }
    };

   private:

    DataStructures *m_dsa;
    DSGraph* m_gDsg;
    DenseMap<const DSNode*, WrapperDSNode> m_nodes;
    DenseMap<const DSNode*, ValueSet> m_referrers_map;
    boost::bimap<const Value*, unsigned int> m_alloc_sites;

    void addNode (const DSNode* n);

    void insertReferrersMap (const DSNode* n, const Value* v); 

    bool hasReferrers (const DSNode* n) const;

    const ValueSet& getReferrers (const DSNode* n) const; 

    bool addAllocSite (const Value* v, unsigned int & site_id); 

    void countAccesses (const DataLayout* dl, const TargetLibraryInfo* tli,
                        DSGraph* dsg, Value* V);
                        
    void findDSNodeForValue(const Value* v, std::set<unsigned int>& nodes);

    void writeDSAnalysisInfo(llvm::raw_ostream& o);

    void writeAllocSitesInfo(llvm::raw_ostream& o, bool isFile);

  public:
 
    static char ID;
    
    DSAInfo ();

    DataStructures * getDSA () { return m_dsa; }

    // whether the DSNode is ever read or written
    bool isAccessed (const DSNode* n) const;

    // return unique numeric identifier for DSNode
    unsigned int getDSNodeID (const DSNode* n) const;

    // return unique numeric identifier for Value if it is an
    // allocation site, otherwise 0.
    const unsigned int getAllocSiteID (const Value* V) const;

    // the inverse of getAllocSiteID
    const Value* getAllocValue (unsigned int alloc_site_id) const;

    virtual bool runOnModule (llvm::Module &M);

    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;

    void releaseMemory();

    virtual const char* getPassName () const {return "DSAInfo";}

  };
}
#endif 
#endif
