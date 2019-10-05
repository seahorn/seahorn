#ifndef _HORN_CLAUSE_DB_WTO__H_
#define _HORN_CLAUSE_DB_WTO__H_

#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/Stats.hh"

#include "seahorn/HornClauseDBBgl.hh"
#include "seahorn/Analysis/WeakTopologicalOrder.hh"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn
{
  using namespace llvm;
  using namespace expr;

   namespace wto_impl {
      template<>
      inline void write_graph_vertex(llvm::raw_ostream&o, Expr fdecl) {
        o << *(bind::fname(fdecl));
      }
   }

  // Build a weak topological ordering from the Horn clause database.
  class HornClauseDBWto {
    typedef WeakTopoOrder<HornClauseDBCallGraph> wto_t;

    HornClauseDBCallGraph &m_callgraph;
    wto_t m_wto;

   public:

    typedef typename wto_t::iterator iterator;
    typedef typename wto_t::const_iterator const_iterator;

    typedef typename wto_t::nested_components_iterator head_iterator;
    typedef typename wto_t::nested_components_const_iterator head_const_iterator;

    HornClauseDBWto(HornClauseDBCallGraph &callgraph): m_callgraph(callgraph) { }

    // -- iterators to traverse the wto
    iterator begin () {  return m_wto.begin(); }
    iterator end () {  return m_wto.end(); }

    const_iterator begin () const {  return m_wto.begin(); }
    const_iterator end () const {  return m_wto.end(); }

    // -- iterators to traverse the heads of the nested
    // -- components. The heads are sorted in such way that the first
    // -- corresponds to the outermost component and the last to the
    // -- innermost component.

    head_iterator heads_begin (Expr fdecl)
    { return m_wto.nested_components_begin(fdecl); }
    head_iterator heads_end (Expr fdecl)
    { return m_wto.nested_components_end(fdecl); }

    head_const_iterator heads_begin (Expr fdecl) const
    { return m_wto.nested_components_begin(fdecl); }
    head_const_iterator heads_end (Expr fdecl) const
    { return m_wto.nested_components_end(fdecl); }

    void buildWto () {

      Stats::resume ("wto");

      m_callgraph.buildCallGraph();

      if (!m_callgraph.hasEntry()) {
        errs () << "wto requires an entry point to the call graph\n";
        return;
      }

      m_wto.buildWto(&m_callgraph, m_callgraph.entry());

      Stats::stop ("wto");

      LOG("horn-wto",
          errs () << "WTO="; m_wto.write(errs()); errs () << "\n";);

      LOG("horn-wto",
          for (auto fdecl: m_callgraph.m_db.getRelations ()) {
            errs () << "Heads of the wto nested components for "
                    << *(bind::fname(fdecl)) << "={";
            auto it = heads_begin(fdecl);
            auto et = heads_end(fdecl);
            for (; it!=et;) {
              auto head = *it;
              errs () << *(bind::fname(head));
              ++it;
              if (it !=et)
                errs () << ",";
            }
            errs () << "}\n";
          });
    }

  };
}
#endif /* _HORN_CLAUSE_DB_WTO__H_ */
