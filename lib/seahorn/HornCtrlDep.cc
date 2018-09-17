#include "seahorn/HornCtrlDep.hh"
#include <iostream>
// static void debug_breakpoint()
// {
//   llvm::errs()<<"******* entering debug break point******\n";
// }

namespace seahorn
{
  using namespace expr;
  HornDomTree::HornDomTree(HornClauseDB& hcdb, HornClauseDBCallGraph &hccg, bool reverse)
  : db(hcdb), cg(hccg), reverse(reverse), false_expr(mk<FALSE>(db.getExprFactory()))
  {
    HornClauseDB::expr_set_type rels = db.getRelations();
    for (Expr rel : rels)
    {
      dom_map.emplace(std::piecewise_construct, 
        std::forward_as_tuple(rel), 
        std::forward_as_tuple(rels.begin(), rels.end()));
    }
    Expr entry = cg.entry();
    if (reverse) {
      // assume exit node is query
      entry = db.getQueries()[0]->left();
    }

    // compute dom_map
    ExprSet worklist;
    worklist.insert(entry);
    while (worklist.size())
    {
      Expr rel = *worklist.begin();
      worklist.erase(worklist.begin());

      ExprSet new_dom;
      bool first_pred = true;
      
      const auto& callers_set = cg.callers(rel);
      const auto& callees_set = cg.callees(rel);
      
      // make copy: callers/callees return reference
      ExprSet pred_set(callers_set.begin(), callers_set.end());
      ExprSet succ_set(callees_set.begin(), callees_set.end());

      if (reverse) pred_set.swap(succ_set);
      
      for (auto pred: pred_set)
      {
        if (first_pred)
        {
          new_dom.insert(dom_map[pred].begin(), dom_map[pred].end());
          first_pred = false;
        }
        else
        {
          ExprSet tmp_dom;
          std::set_intersection(new_dom.begin(), new_dom.end(), dom_map[pred].begin(), dom_map[pred].end(),
            std::inserter(tmp_dom, tmp_dom.end()));
          new_dom = std::move(tmp_dom);
        }
      }
      new_dom.insert(rel);
      if (new_dom != dom_map[rel])
      {
        dom_map[rel] = std::move(new_dom);
        for (auto succ: succ_set)
          worklist.insert(succ);
      }
    }

    // ENodeUniqueEqual expr_eq;

    // compute idom_map
    for (auto& p : dom_map)
    {
      auto sdom_set = p.second;
      sdom_set.erase(p.first);

      for (auto sdom: sdom_set)
      {
        if (std::includes(dom_map[sdom].begin(), dom_map[sdom].end(), 
          sdom_set.begin(), sdom_set.end()))
        {
          idom_map[p.first] = sdom;
          break;
        }
      }
    }
  }
  Expr HornDomTree::immDom(Expr fdecl)
  {
     auto it = idom_map.find(fdecl);
    if (it == idom_map.end()) return false_expr;
    return it->second; 
  }
  const ExprSet& HornDomTree::allDom(Expr fdecl) 
  {
    auto it = dom_map.find(fdecl);
    if (it == dom_map.end()) return empty_set;
    return it->second;
  }
  
  HornCtrlDep::HornCtrlDep(HornClauseDB& hcdb, HornClauseDBCallGraph& hccg) : db(hcdb), cg(hccg), pdt(db, cg, true) 
  {
    for (const HornRule& rule : db.getRules())
    {
      if (!isOpX<AND>(rule.body())) continue;
      /// execution from A to B, CFG edge A->B
      Expr A = rule.body()->left()->left();
      Expr B = rule.head()->left();

      /// B does not post-dominate Ap
      if (pdt.allDom(A).count(B)) continue;
      /// L is the LCA of A and B on PDT
      Expr L = pdt.immDom(A);
      ENodeUniqueEqual expr_eq;
      do {
        // should be unique
        cd_map.insert(std::make_pair(B, A));
        B = pdt.immDom(B);
      } while (!expr_eq(B.get(), L.get()));
    }

    // CFG p->q  <==> (HornClauseDB::expr_set_type) q in cg.callees(p)

    for (Expr rel: db.getRelations())
    {
      std::cerr<<"=== "<<*(rel->left())<<" is CTRL DEP on ";
      Expr cd = cd_map[rel];
      if (cd) std::cerr<<*(cd->left())<<"\n";
      else std::cerr<<"(null) \n";
    };

  }
  Expr HornCtrlDep::ctrlDep(Expr fdecl)
  {
    return cd_map[fdecl];
  }
}