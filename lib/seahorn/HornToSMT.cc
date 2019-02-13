#include "seahorn/HornToSMT.hh"
#include "seahorn/HornClauseDBBgl.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include <boost/lexical_cast.hpp>
#include <boost/graph/reverse_graph.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/breadth_first_search.hpp>
#include <deque>

namespace seahorn
{
    using namespace expr;
    using namespace ufo;
    namespace
    {
        struct append_tag
        {
            std::string tag_str;
            append_tag(const std::string& str): tag_str(str) {}
            Expr operator() (Expr var) const
            {
                if (!bind::IsConst()(var)) return nullptr;
                Expr fdecl = var->left();
                Expr name = bind::fname(fdecl);
                name = variant::tag(name, tag_str);
                fdecl = bind::rename(fdecl, name);
                return bind::fapp(fdecl);
            }
        };
        struct replace_or_tag
        {
            ExprMapPtr var_map;
            size_t& var_cnt;
            replace_or_tag(ExprMapPtr map, size_t& cnt): var_map(map), var_cnt(cnt) {}
            Expr operator() (Expr e) const
            {
                if (!bind::IsConst()(e)) return nullptr;
                auto it = var_map->find(e);
                if (it == var_map->end())
                {
                    Expr tagged_e = append_tag(lexical_cast<std::string>(var_cnt++))(e);
                    var_map->insert(std::make_pair(e, tagged_e));
                    return tagged_e;
                }
                else return it->second;
            }
        };

        ExprMapPtr create_var_map(Expr std_fapp, Expr caller_fapp)
        {
            ExprMapPtr var_map = std::make_shared<ExprMap>();
            auto it_std = std_fapp->args_begin();
            auto it_this = caller_fapp->args_begin();
            for (++it_std, ++it_this; it_std != std_fapp->args_end(); ++it_std, ++it_this)
            {
                // LOG("horn-smt", outs()<<"=== map "<<**it_this<<" to "<<**it_std<<" ===\n");
                var_map->insert(std::make_pair(*it_this, *it_std));
            }
            return var_map;
        }

        Expr add_glue_code(Expr conj, Expr this_fapp, Expr std_fapp)
        {
            ENodeUniqueEqual eq;
            if (eq(this_fapp.get(), std_fapp.get())) return conj;

            // LOG("horn-smt", outs()<<"== conj: "<<*conj<<" this_fapp: "<<*this_fapp<<" std_fapp: "<<*std_fapp<<" ==\n");

            ExprVector clauses(conj->args_begin(), conj->args_end());
            ENode::args_iterator it_std = ++(std_fapp->args_begin());
            ENode::args_iterator it_this = ++(this_fapp->args_begin());
            
            while (it_std != std_fapp->args_end())
            {
                if (!eq(*it_std, *it_this)){
                    Expr std_arg = *it_std;
                    Expr this_arg = *it_this;
                    clauses.push_back(mk<EQ>(std_arg, this_arg));
                }
                ++it_std;
                ++it_this;
            }
            return boolop::land(clauses);
        }

        Expr create_std_fapp(Expr fapp, size_t &var_cnt)
        {
            // fapp = fapp(rel)
            Expr std_fapp = fapp;
            Expr rel = fapp->left();
            // has args, create new args
            size_t n_args = bind::domainSz(rel);
            if (n_args)
            {
                ExprVector std_args;
                for (auto it = ++(fapp->args_begin()); it != fapp->args_end(); ++it)
                    std_args.push_back(append_tag(lexical_cast<std::string>(var_cnt++))(*it));
                assert(std_args.size() == n_args);
                std_fapp = bind::fapp(rel, std_args);
            }
            return std_fapp;
        }

        class horn_rule_visitor : boost::default_bfs_visitor
        {
        private:
            ZSolver<EZ3> & solver;
            ExprMap & assert_map;
            std::map<ExprPair, Expr> & smt_rule_map;
            Expr false_expr;
        public:
            typedef boost::reverse_graph<HornClauseDBCallGraph> graph_t;
            typedef typename boost::graph_traits<graph_t>::edge_descriptor rev_edge_t; // reverse_graph_edge_descriptor<EdgeDesc>
            typedef typename boost::graph_traits<graph_t>::vertex_descriptor vertex_t;

            horn_rule_visitor(ZSolver<EZ3> & solver_ref, ExprMap & assert_map_ref, std::map<ExprPair, Expr> & smt_rule_map_ref, Expr f)
            : solver(solver_ref), assert_map(assert_map_ref), smt_rule_map(smt_rule_map_ref), false_expr(f) {}

            void discover_vertex(const vertex_t& v, const graph_t& g)
            {
                LOG("horn-smt", outs()<<"=== DISCOVER VERTEX: "<<*(bind::fname(v))<<" ===\n");
                assert_map.insert(std::make_pair(v, false_expr));
            }
            
            void examine_edge(const rev_edge_t& rev_e, const graph_t& g)
            {
                auto e = rev_e.underlying_descx;
                LOG("horn-smt", outs()<<"=== EXAMINE EDGE: "<<*(bind::fname(e.first))<<" ---> "<<*(bind::fname(e.second))<<" ===\n");
                Expr cond = boolop::lor(assert_map[e.first], 
                                boolop::land(bind::boolConst(e.second->left()), smt_rule_map[e]));
                assert_map[e.first] = cond;
            }
            
            void finish_vertex(const vertex_t& v, const graph_t& g)
            {
                Expr assertion = boolop::limp(bind::boolConst(v->left()), assert_map[v]);
                solver.assertExpr(assertion);
                assert_map.erase(v);
            }
        };
    }

    Expr HornToSMT::get_std_fapp(Expr fapp)
    {
        Expr std_fapp;
        Expr rel = fapp->left();
        auto find_it = std_fapp_map.find(rel);
        if (find_it == std_fapp_map.end())
        {
            std_fapp = create_std_fapp(fapp, var_cnt);
            std_fapp_map.insert(std::make_pair(rel, std_fapp));
        }
        else std_fapp = find_it->second;
        return std_fapp;
    }

    void HornToSMT::toSMT(ZSolver<EZ3> &solver)
    {
        var_cnt = 0;
        std_fapp_map.clear();
        smt_rule_map.clear();


        for (HornRule& rule : db.getRules())
        {
            //  TRUE => callee
            int arity = rule.body()->arity();
            if (arity == 0) continue;
            
            Expr callee_rel = rule.head()->left();
            assert(isOpX<FDECL>(callee_rel));

            Expr caller_fapp = rule.body();

            Expr rule_body = mk<TRUE>(db.getExprFactory());

            if (arity == 2)
            {
                caller_fapp = caller_fapp->left();
                rule_body = rule.body()->right();
            }

            Expr caller_rel = caller_fapp->left();

            LOG("horn-smt", outs()<<"=== translating rule: "<<*(bind::fname(caller_rel))<<" ---> "<<*(bind::fname(callee_rel))<<" ===\n");
            
            // instantiate concrete args for both caller and callee
            Expr std_caller_fapp = get_std_fapp(caller_fapp);
            Expr std_callee_fapp = get_std_fapp(rule.head());

            ExprMapPtr var_map;
            auto find_it = var_map_map.find(caller_rel);
            if (find_it == var_map_map.end())
            {
                var_map = create_var_map(std_caller_fapp, caller_fapp);
                if (isOpX<TAG>(caller_rel->left())) // create new copies of temp vars
                    rule_body = replace(rule_body, mk_fn_map(replace_or_tag(var_map, var_cnt)));
                else // keep temp vars
                    rule_body = replace(rule_body, *var_map);
                var_map_map.insert(std::make_pair(caller_rel, var_map));
            }
            else
            {
                var_map = find_it->second;
                rule_body = replace(rule_body, *var_map);
            }
            
            Expr rule_head = replace(rule.head(), *var_map);
            rule_body = add_glue_code(rule_body, rule_head, std_callee_fapp);

            LOG("horn-smt", outs()<<"=== rule body: "<<*(rule_body)<<" ===\n");
            smt_rule_map.insert(std::make_pair(std::make_pair(caller_rel, callee_rel), rule_body));
        }

        db.buildIndexes();
        HornClauseDBCallGraph cg(db);
        cg.buildCallGraph();
        Expr query = db.getQueries()[0];
        solver.assertExpr(query);
        solver.assertExpr(bind::fapp(cg.entry()));

        std::deque<Expr> Q;
        ExprSet completed;
        Q.push_back(query->left());
        completed.insert(query->left());
        completed.insert(cg.entry());
        while (!Q.empty())
        {
            Expr callee_rel = Q.front();
            LOG("horn-smt", outs()<<"=== DISCOVER VERTEX: "<<*(bind::fname(callee_rel))<<" ===\n");
            Q.pop_front();
            
            // if (boost::in_degree(callee_rel, cg) == 0) continue;
            LOG("horn-smt", outs()<<"=== in degree: "<<boost::in_degree(callee_rel, cg)<<" ===\n");

            Expr cond = mk<FALSE>(db.getExprFactory());
            
            // auto it_pair = boost::in_edges(callee_rel, cg);
            for (Expr caller_rel : cg.callers(callee_rel))
            // for (auto it = it_pair.first; it != it_pair.second; ++it)
            {
                // Expr caller_rel = it->first;

                LOG("horn-smt", outs()<<"=== EXAMINE EDGE: "<<*(bind::fname(caller_rel))<<" ---> "<<*(bind::fname(callee_rel))<<" ===\n");

                cond = boolop::lor(cond, 
                    boolop::land(bind::boolConst(caller_rel->left()), smt_rule_map[std::make_pair(caller_rel, callee_rel)]));
                if (!completed.count(caller_rel))
                {
                    completed.insert(caller_rel);
                    Q.push_back(caller_rel);
                }
            }
            solver.assertExpr(boolop::limp(bind::boolConst(callee_rel->left()), cond));
        }


        // auto rcg = boost::make_reverse_graph(cg);

        // ExprMap tmp_map;
        // Expr f = mk<FALSE>(db.getExprFactory());
        // horn_rule_visitor vis(solver, tmp_map, smt_rule_map, f);

        // boost::breadth_first_search(rcg, query->left(), boost::visitor(vis));

        // outs()<<"=========BEGIN SMT===========\n";
        // solver.toSmtLib(outs());
        // outs()<<"=========END SMT===========\n";

        boost::tribool res = solver.solve();

        if (res) LOG("horn-smt", errs()<<"=== SAT ===\n";);
        else if (!res) LOG("horn-smt", errs()<<"=== UNSAT ===\n";);
        else LOG("horn-smt", errs()<<"=== UNKNOWN ===\n";);
    }
  

}
