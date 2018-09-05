#include "seahorn/TaintTracker.hh"
#include "boost/function_output_iterator.hpp"
#include <utility>
#include "llvm/Support/CommandLine.h"

#include "avy/AvyDebug.h"
#include "ufo/Expr.hpp"

// using namespace llvm;
static llvm::cl::opt<bool>
TaintControl ("taint-control", llvm::cl::Hidden, llvm::cl::init (true));

namespace seahorn
{
  using namespace expr;
  using namespace std;
  using namespace ufo;

  namespace 
  {
    bool is_cond(Expr e)
    {
      return (bind::isBoolConst(e) || isOpX<NEG>(e));
    }
  }
  
  Expr TaintTracker::get_br_cond(Expr rel, HornToSMT::rule_map_type &rules)
  {
    auto& callees = cg.callees(rel);
    if (callees.size() != 2) return nullptr;
    auto it = callees.begin();
    Expr r1 = *it;
    Expr r2 = *(++it);
    ExprPair p1 = make_pair(rel, r1), p2 = make_pair(rel, r2);
    Expr r1_conj = rules[p1];
    Expr r2_conj = rules[p2];
    
    ExprSet r1_cond, r2_cond;
    copy_if(r1_conj->args_begin(), r1_conj->args_end(), inserter(r1_cond, r1_cond.end()), is_cond);
    copy_if(r2_conj->args_begin(), r2_conj->args_end(), inserter(r2_cond, r2_cond.end()), is_cond);

    ExprVector cond;
    set_symmetric_difference(r1_cond.begin(), r1_cond.end(), r2_cond.begin(), r2_cond.end(), inserter(cond, cond.end()));
    
    Expr cond_var = bind::isBoolConst(cond[0]) ? cond[0] : cond[1];

    branch_dir_map[p1] = (r1_cond.count(cond_var) == 1);
    branch_dir_map[p2] = !branch_dir_map[p1];
    return cond_var;
  }

  void TaintTracker::toSMT(ZSolver<EZ3> &solver)
  {
    for (auto& p: taint_rule_map)
    {
      Expr caller = p.first.first, callee = p.first.second;
      size_t br = cg.callees(caller).size();
      Expr cond;
      if (br == 1) cond = bind::boolConst(caller->left());
      else if (br == 2)
      {
        Expr cond_var = branch_cond_map[caller];
        Expr br_dir = branch_dir_map[p.first]? cond_var: boolop::lneg(cond_var);
        cond = boolop::land(bind::boolConst(caller->left()), br_dir);
      }
      solver.assertExpr(boolop::limp(cond, p.second));
    }
  }
  Expr TaintTracker::get_taint_var(Expr prog_var)
  {
    assert(bind::IsConst()(prog_var));
    auto search = taint_var_map.find(prog_var);
    Expr taint_var;
    
    if (search != taint_var_map.end())
      taint_var = search->second;
    else {
      Expr fdecl = bind::fname(prog_var);
      Expr new_name = variant::tag(bind::fname(fdecl), "t");
      // LOG("taint-tracker", cerr<<"=== var name:"<<*(bind::fname(fdecl))<<" new name: "<<*(new_name)<<" ===\n");
      taint_var = bind::boolConst(new_name);
      taint_var_map.insert(make_pair(prog_var, taint_var));
    }
    LOG("taint-tracker", cerr<<"=== var: "<<*(prog_var)<<" taint var: "<<*(taint_var)<<" ===\n");
    return taint_var;
  }

  Expr TaintTracker::get_ite_taint(Expr ite)
  {
    ExprVector cond_list, then_list, else_list;
    get_taint_list(ite->arg(0), cond_list);
    get_taint_list(ite->arg(1), then_list);
    get_taint_list(ite->arg(2), else_list);
    return boolop::lor(mk_or_expr(cond_list), 
      boolop::lite(ite->arg(0), mk_or_expr(then_list), mk_or_expr(else_list)));
  }

  Expr TaintTracker::get_control_taint(Expr rel)
  {
    if (!TaintControl) return false_expr;
    Expr cd = cdg.ctrlDep(rel);

    ExprVector cond_taint_list;
    while (cd.get())
    {
      Expr cond_var = branch_cond_map[cd];
      if (cond_var.get()) cond_taint_list.push_back(get_taint_var(cond_var));
      cd = cdg.ctrlDep(cd);
    }
    return mk_or_expr(cond_taint_list);
  }
  void TaintTracker::applyTaint(HornToSMT &smt)
  {
    taint_var_map.clear();
    taint_rule_map.clear();
    branch_cond_map.clear();
    auto& smt_rules = smt.get_smt_rules();

    for (Expr rel: db.getRelations())
    {
      Expr cond_var = get_br_cond(rel, smt_rules);
      if (!cond_var.get()) continue;
      branch_cond_map.insert(make_pair(rel, cond_var));
      LOG("taint-tracker", cerr<<"=== branch:"<<*(rel->left())<<", cond:"<<*(cond_var)<<" ===\n");
    }
    
    for (auto& p : smt_rules)
    {
      Expr caller = p.first.first, callee = p.first.second, rule_body = p.second;
      Expr ct = get_control_taint(caller);
      ExprVector assign_list;
      for (Expr assign: boost::make_iterator_range(rule_body->args_begin(), rule_body->args_end()))
      {
        if (!isOpX<EQ>(assign) && !isOpX<IFF>(assign)) continue;

        LOG("taint-tracker", cerr<<"=== assignment :"<<*(assign)<<" ===\n");
        
        Expr prog_var = assign->left(), prog_expr = assign->right();
        
        Expr taint_var = get_taint_var(prog_var), taint_expr;

        if (isOpX<ITE>(prog_expr)) 
        {
          taint_expr = get_ite_taint(prog_expr);
        }
        else
        {
          ExprVector taint_list;
          get_taint_list(prog_expr, taint_list);
          taint_expr = mk_or_expr(taint_list);
        }
        assign_list.push_back(mk<EQ>(taint_var, boolop::lor(ct, taint_expr)));
      }
      if (!assign_list.size()) continue;
      Expr taint_rule = boolop::land(assign_list);
      ExprPair key = make_pair(caller, callee);
      taint_rule_map.insert(make_pair(key, taint_rule));
    }
  }

  void TaintTracker::get_taint_list(Expr e, ExprVector& v)
  {
    filter(e, bind::IsConst(), boost::make_function_output_iterator(
          [this, &v](Expr var){
            Expr t = get_taint_var(var);
            v.push_back(t);
          }));
  }

  // void TaintTracker::applyTaint(HornClauseDB &db, HornCtrlDep &cdg, vector<HornRule> new_rules)
  // {
     
  // }
}