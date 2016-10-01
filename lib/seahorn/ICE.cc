#include "seahorn/ICE.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/GuessCandidates.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include <vector>
#include <boost/logic/tribool.hpp>
#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>
#include <boost/optional/optional.hpp>
#include <boost/tokenizer.hpp>
#include "boost/range/algorithm/reverse.hpp"
#include "seahorn/HornClauseDBWto.hh"
#include <algorithm>

#include "ufo/Stats.hh"

#include <iostream>
#include <string>

#include <stdlib.h>
#include <stdio.h>

using namespace llvm;

namespace seahorn
{
  #define SAT_OR_INDETERMIN true
  #define UNSAT false

  #define NAIVE 0
  #define EACH_RULE_A_SOLVER 1
  #define EACH_RELATION_A_SOLVER 2

  /*ICEPass methods begin*/

  char ICEPass::ID = 0;

  bool ICEPass::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    //Use commandline option to replace it.
    int config = NAIVE;

    Stats::resume ("ICE inv");
    ICE ice(hm);
    ice.setupC5();
    ice.genInitialCandidates(hm.getHornClauseDB());
    ice.runICE(config);
    outs() << "RUN ICE SUCCESSCULLY\n";
    Stats::stop ("ICE inv");

    return false;
  }

  void ICEPass::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  /*ICEPass methods end*/

  /*ICE methods begin*/

  void ICE::addInvarCandsToProgramSolver()
  {
	  auto &db = m_hm.getHornClauseDB();
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr cand_app = m_candidate_model.getDef(fapp);
		  LOG("candidates", errs() << "HEAD: " << *fapp << "\n";);
		  LOG("candidates", errs() << "CAND: " << *cand_app << "\n";);
		  if(!isOpX<TRUE>(cand_app))
		  {
			  LOG("candidates", errs() << "ADD CONSTRAINT\n";);
			  db.addConstraint(fapp, cand_app);
		  }
	  }
  }

  //Set .names file and .interval file
  void ICE::setupC5()
  {
	  m_C5filename = "FromCmd";

	  std::ofstream names_of(m_C5filename + ".names");
	  if(!names_of)return;

	  std::ofstream intervals_of(m_C5filename + ".intervals");
	  if(!intervals_of)return;

	  int lowerInterval = 2;
	  int upperInterval = 2;

	  //convert predicate names to the name format of C5
	  auto &db = m_hm.getHornClauseDB();
	  int rel_index = 0;
	  for(Expr rel : db.getRelations())
	  {
		  Expr C5_rel_name = variant::variant(rel_index, mkTerm<std::string>(std::string("PRED"), rel->efac()));
		  m_rel_to_c5_rel_name_map.insert(std::make_pair(bind::fname(rel), C5_rel_name));
		  m_c5_rel_name_to_rel_map.insert(std::make_pair(C5_rel_name, bind::fname(rel)));
		  rel_index ++;
	  }

	  outs() << "REL NAME TO C5 NAME MAP:\n";
	  for(auto it = m_rel_to_c5_rel_name_map.begin(); it != m_rel_to_c5_rel_name_map.end(); ++it)
	  {
		  outs() << *(it->first) << ", " << *(it->second) << "\n";
	  }

	  names_of << "invariant.\n";

	  //first attribute is the predicate names
	  names_of << "$pc: ";
	  int counter=0;
	  for(Expr rel : db.getRelations())
	  {
		  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
		  if(counter == db.getRelations().size()-1)
		  {
			  names_of << *C5_rel_name << ".\n";
		  }
		  else
		  {
			  names_of << *C5_rel_name << ",";
		  }
		  counter++;
	  }

	  //each argument of each predicate is an attribute
	  for(Expr rel : db.getRelations())
	  {
		  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  if(isOpX<INT_TY>(bind::domainTy(rel, i)) || isOpX<BOOL_TY>(bind::domainTy(rel, i)))
			  {
				  Expr arg_i_type = bind::domainTy(rel, i);
				  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
				  Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
				  m_attr_name_to_expr_map.insert(std::make_pair(attr_name_i, arg_i));
				  names_of << attr_name_i << ": continuous.\n";
				  upperInterval ++;
			  }
			  else
			  {
				  outs() << "NOT INT OR BOOL TYPE!\n";
			  }
		  }
		  //implicit attributes which have the form x1 +/- x2
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  for(int j=i+1; j<bind::domainSz(rel); j++)
			  {
				  if(isOpX<INT_TY>(bind::domainTy(rel, i)) && isOpX<INT_TY>(bind::domainTy(rel, j)))
				  {
					  Expr arg_type = bind::domainTy(rel, i);
					  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_type));
					  Expr arg_j = bind::fapp(bind::constDecl(variant::variant(j, mkTerm<std::string> ("V", rel->efac ())), arg_type));
					  Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
					  Expr attr_name_j = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_j)));
					  names_of << attr_name_i << "+" << attr_name_j << ":= " << attr_name_i << " + " << attr_name_j << ".\n";
					  names_of << attr_name_i << "-" << attr_name_j << ":= " << attr_name_i << " - " << attr_name_j << ".\n";
					  upperInterval += 2;
				  }
			  }
		  }

		  std::string interval_line;
		  if(bind::domainSz(rel) == 0)
		  {
			  interval_line = boost::lexical_cast<std::string>(lowerInterval) + " " + boost::lexical_cast<std::string>(upperInterval) + "\n";
		  }
		  else
		  {
			  interval_line = boost::lexical_cast<std::string>(lowerInterval) + " " + boost::lexical_cast<std::string>(upperInterval - 1) + "\n";
		  }
		  intervals_of << interval_line;
		  lowerInterval = upperInterval;
		  upperInterval = lowerInterval;
	  }

      names_of << "invariant: true, false.\n";
	  names_of.close();
	  intervals_of.close();
  }

  void ICE::genInitialCandidates(HornClauseDB &db)
  {
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr True = mk<TRUE>(rel->efac());

		  outs() << *fapp << "\n";
		  m_candidate_model.addDef(fapp, True);
	  }
  }

  void ICE::C5learn()
  {
	  generateC5DataAndImplicationFiles();

	  outs() << "DATA & IMPL FILES ARE GENERATED\n";

	  FILE *fp;
	  FILE *wp;
	  wp = fopen("C5_temp","w+");
	  std::string command = "/home/chenguang/Desktop/C50-ICE/C50/c5.0.dt_penalty -I 1 -m 1 -f " + m_C5filename;
	  //std::string command = "/home/chenguang/Desktop/C50-ICE/C50/c5.0.dt_penalty -I 1 -f " + m_C5filename;
	  std::string access = "r";
	  if((fp = popen(command.c_str(), access.c_str())) == NULL)
	  {
		  perror("popen failed!\n");
		  return;
	  }
	  char buf[1024];

	  size_t status = fread(buf, sizeof(char), sizeof(buf), fp);
	  if(status == 0)
	  {
		  outs() << "read from popen failed!\n";
		  return;
	  }
	  fwrite(buf, 1, sizeof(buf), wp);

	  pclose(fp);
	  fclose(wp);

	  //parse the .json file to ptree
	  std::ifstream if_json(m_C5filename + ".json");
	  std::ostringstream json_buf;

	  char ch;
	  while(json_buf && if_json.get(ch))
	  { json_buf.put(ch); }

	  std::string json_string =  json_buf.str();

	  boost::property_tree::ptree pt;
	  std::stringstream ss(json_string);
	  try
	  { boost::property_tree::json_parser::read_json(ss, pt); }
	  catch(boost::property_tree::ptree_error & e)
	  { outs() << "READ JSON ERROR!\n"; return; }

	  //parse ptree to invariant format
	  convertPtreeToInvCandidate(pt);

	  outs() << "NEW CANDIDATES MAP:\n";
	  auto &db = m_hm.getHornClauseDB();
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr cand = m_candidate_model.getDef(fapp);
		  outs() << *fapp << " : " << *cand << "\n";
	  }
  }

  void ICE::convertPtreeToInvCandidate(boost::property_tree::ptree pt)
  {
	  auto &db = m_hm.getHornClauseDB();
	  //if only have the root node
	  if(pt.get<std::string>("children") == std::string("null"))
	  {
		  outs() << "PT HAS NO CHILDREN\n";
		  Expr candidate;
		  if(pt.get<std::string>("classification") == "true" || pt.get<std::string>("classification") == "True")
		  {
			 candidate = mk<TRUE>(db.getExprFactory());
		  }
		  else if(pt.get<std::string>("classification") == "false" || pt.get<std::string>("classification") == "False")
		  {
			 candidate = mk<FALSE>(db.getExprFactory());
		  }
		  for(Expr rel : db.getRelations())
		  {
			  ExprVector arg_list;
			  for(int i=0; i<bind::domainSz(rel); i++)
			  {
				  Expr arg_i_type = bind::domainTy(rel, i);
				  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
				  arg_list.push_back(arg_i);
			  }
			  Expr fapp = bind::fapp(rel, arg_list);
			  m_candidate_model.addDef(fapp, candidate);
		  }
		  return;
	  }

	  boost::property_tree::ptree children = pt.get_child("children");
	  auto rels_it = db.getRelations().begin();
	  for(auto child_it : children)
	  {
		  Expr candidate;

		  Expr rel = *rels_it;
		  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
		  std::ostringstream oss;
		  oss << C5_rel_name;
		  outs() << "TAG: " << oss.str() << "\n";

		  boost::property_tree::ptree sub_pt = child_it.second;
		  if(sub_pt.get<std::string>("children") == std::string("null"))
		  {
			  if(sub_pt.get<std::string>("classification") == "true" || sub_pt.get<std::string>("classification") == "True")
			  {
				 candidate = mk<TRUE>(db.getExprFactory());
			  }
			  else if(sub_pt.get<std::string>("classification") == "false" || sub_pt.get<std::string>("classification") == "False")
			  {
				 candidate = mk<FALSE>(db.getExprFactory());
			  }
		  }
		  else
		  {
			  std::list<Expr> stack;
			  stack.push_back(mk<TRUE>(db.getExprFactory()));
			  std::list<std::list<Expr>> final_formula = constructFormula(stack, sub_pt);
			  ExprVector disjunctions;
			  for(std::list<std::list<Expr>>::iterator disj_it = final_formula.begin(); disj_it != final_formula.end(); ++disj_it)
			  {
				  ExprVector conjunctions;
				  for(std::list<Expr>::iterator conj_it = (*disj_it).begin(); conj_it != (*disj_it).end(); ++conj_it)
				  {
					  conjunctions.push_back(*conj_it);
				  }
				  Expr disjunct = mknary<AND>(conjunctions.begin(), conjunctions.end());
				  disjunctions.push_back(disjunct);
			  }
			  if(disjunctions.size() == 1)
			  {
				  candidate = disjunctions[0];
			  }
			  else
			  {
				  candidate = mknary<OR>(disjunctions.begin(), disjunctions.end());
			  }
		  }
		  outs() << "NEW CANDIDATE: " << *candidate << "\n";

		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);

		  m_candidate_model.addDef(fapp, candidate);
		  rels_it++;
	  }
  }

  std::list<std::list<Expr>> ICE::constructFormula(std::list<Expr> stack, boost::property_tree::ptree sub_pt)
  {
	  Expr decision_expr;
	  std::list<std::list<Expr>> final_formula;
	  //leaf node
	  if(sub_pt.get<std::string>("children") == std::string("null"))
	  {
		  outs() << "LEAF NODE\n";
		  if(sub_pt.get<std::string>("classification") == "true" || sub_pt.get<std::string>("classification") == "True")
		  {
			 std::list<Expr> new_conjunct = stack;
			 final_formula.push_back(new_conjunct);
			 return final_formula;
		  }
		  else if(sub_pt.get<std::string>("classification") == "false" || sub_pt.get<std::string>("classification") == "False")
		  {
			 return final_formula;
		  }
	  }
	  //internal node
	  else
	  {
		  outs() << "INTERNAL NODE\n";
		  std::string attr_name = sub_pt.get<std::string>("attribute");
		  outs() << "CUT ATTRIBUTE: " << attr_name << "\n";

		  typedef boost::tokenizer< boost::char_separator<char>> t_tokenizer;
		  if(attr_name.find("+") != -1)
		  {
			  boost::char_separator<char> sep("+");
			  t_tokenizer tok(attr_name, sep);
			  std::string left_name = *(tok.begin());
			  std::string right_name = *(++tok.begin());
			  Expr left_expr;
			  Expr right_expr;
			  for(ExprMap::iterator it = m_attr_name_to_expr_map.begin(); it!= m_attr_name_to_expr_map.end(); ++it)
			  {
				  std::ostringstream oss;
				  oss << *(it->first);
				  if(oss.str() == left_name)
				  {
					  left_expr = it->second;
				  }
				  if(oss.str() == right_name)
				  {
					  right_expr = it->second;
				  }
			  }
			  if(!bind::isIntConst(left_expr) || !bind::isIntConst(right_expr))
			  {
				  outs() << "OPERAND TYPE WRONG!\n";
				  return final_formula;
			  }
			  int cut = sub_pt.get<int>("cut");
			  Expr threshold = mkTerm<mpz_class>(cut, left_expr->efac());
			  decision_expr = mk<LEQ>(mk<PLUS>(left_expr, right_expr), threshold);
		  }
		  else if(attr_name.find("-") != -1)
		  {
			  boost::char_separator<char> sep("-");
			  t_tokenizer tok(attr_name, sep);
			  std::string left_name = *(tok.begin());
			  std::string right_name = *(++tok.begin());
			  Expr left_expr;
			  Expr right_expr;
			  for(ExprMap::iterator it = m_attr_name_to_expr_map.begin(); it!= m_attr_name_to_expr_map.end(); ++it)
			  {
				  std::ostringstream oss;
				  oss << *(it->first);
				  if(oss.str() == left_name)
				  {
					  left_expr = it->second;
				  }
				  if(oss.str() == right_name)
				  {
					  right_expr = it->second;
				  }
			  }
			  if(!bind::isIntConst(left_expr) || !bind::isIntConst(right_expr))
			  {
				  outs() << "OPERAND TYPE WRONG!\n";
				  return final_formula;
			  }
			  int cut = sub_pt.get<int>("cut");
			  Expr threshold = mkTerm<mpz_class>(cut, left_expr->efac());
			  decision_expr = mk<LEQ>(mk<MINUS>(left_expr, right_expr), threshold);
		  }
		  else
		  {
			  Expr attr_expr;
			  for(ExprMap::iterator it = m_attr_name_to_expr_map.begin(); it!= m_attr_name_to_expr_map.end(); ++it)
			  {
				  std::ostringstream oss;
				  oss << *(it->first);
				  if(oss.str() == attr_name)
				  {
					  attr_expr = it->second;
				  }
			  }

			  if(bind::isBoolConst(attr_expr))
			  {
				 decision_expr = mk<NEG>(attr_expr);
				 int cut = sub_pt.get<int>("cut");
				 assert(cut == 0);
			  }
			  else if(bind::isIntConst(attr_expr))
			  {
				 int cut = sub_pt.get<int>("cut");
				 Expr threshold = mkTerm<mpz_class>(cut, attr_expr->efac());
				 decision_expr = mk<LEQ>(attr_expr, threshold);
			  }
			  else
			  {
				 outs() << "DECISION NODE TYPE WRONG!\n";
				 return final_formula;
			  }
		  }
		  stack.push_back(decision_expr);
		  //assert(sub_pt.children().size() == 2);
		  boost::property_tree::ptree::assoc_iterator child_itr = sub_pt.get_child("children").ordered_begin();
		  std::list<std::list<Expr>> final_formula_left = constructFormula(stack, child_itr->second);
		  stack.pop_back();
		  stack.push_back(mk<NEG>(decision_expr));
		  std::list<std::list<Expr>> final_formula_right = constructFormula(stack, (++child_itr)->second);
		  stack.pop_back();
		  final_formula_left.insert(final_formula_left.end(), final_formula_right.begin(), final_formula_right.end());
		  return final_formula_left;
	  }
	  return final_formula;
  }

  std::string ICE::outputDataPoint(DataPoint p)
  {
	  auto &db = m_hm.getHornClauseDB();
	  std::ostringstream oss;
	  Expr pred_name = p.getPredName();
	  Expr C5_pred_name = m_rel_to_c5_rel_name_map.find(pred_name)->second;
	  oss << C5_pred_name;
	  for(Expr rel : db.getRelations())
	  {
		  if(bind::fname(rel) == pred_name)
		  {
			  for(Expr attr : p.getAttrValues())
			  {
				  oss << "," << *attr;
			  }
		  }
		  else
		  {
			  for(int i=0; i<bind::domainSz(rel); i++)
			  {
				  oss << ",?";
			  }
		  }
	  }
	  return oss.str();
  }

  void ICE::generateC5DataAndImplicationFiles()
  {
	  //generate .data file
	  std::ofstream data_of(m_C5filename + ".data");
	  if(!data_of)return;

	  auto &db = m_hm.getHornClauseDB();

	  for(auto it = m_cex_list.begin(); it!=m_cex_list.end(); ++it)
	  {
		  if(m_pos_data_set.count(*it) != 0)
		  {
			  DataPoint pos_dp = *it;
			  data_of << outputDataPoint(pos_dp);
			  data_of << ",true\n";
		  }
		  else if(m_neg_data_set.count(*it) != 0)
		  {
			  DataPoint neg_dp = *it;
			  data_of << outputDataPoint(neg_dp);
			  data_of << ",false\n";
		  }
		  else if(m_impl_cex_set.count(*it) != 0)
		  {
			  DataPoint impl_dp = *it;
			  data_of << outputDataPoint(impl_dp);
			  data_of << ",?\n";
		  }
	  }

	  data_of.close();

	  //generate .implications file
	  std::ofstream implications_of(m_C5filename + ".implications");
	  if(!implications_of)return;

	  for(std::pair<DataPoint, DataPoint> impl_pair : m_impl_pair_set)
	  {
		  DataPoint start_point = impl_pair.first;
		  std::map<DataPoint, int>::iterator it = m_data_point_to_index_map.find(start_point);
		  assert(it != m_data_point_to_index_map.end());
		  int start_index = it->second;

		  DataPoint end_point = impl_pair.second;
		  std::map<DataPoint, int>::iterator itr = m_data_point_to_index_map.find(end_point);
		  assert(itr != m_data_point_to_index_map.end());
		  int end_index = itr->second;

		  implications_of << start_index << " " << end_index << "\n";
	  }

	  implications_of.close();
  }

  /*
   * Main loop of ICE algorithm
   */
  void ICE::runICE(int config)
  {
	  //load the Horn clause database
	  auto &db = m_hm.getHornClauseDB ();
	  db.buildIndexes ();
	  outs() << "DB: \n" << db;

	  //build the new DB wto
	  HornClauseDBCallGraph callgraph(db);
	  HornClauseDBWto db_wto(callgraph);
	  db_wto.buildWto();

	  //record the number of original rules in DB
	  int orig_rule_num = db.getRules().size();

	  int index = 0;
	  bool isChanged = true;
	  while(isChanged)
	  {
		  isChanged = false;
		  constructQueries(db);

		  outs() << "=========================== POS START ============================\n";
		  for(auto it = m_pos_rule_set.begin(); it != m_pos_rule_set.end(); ++it)
		  {
			  HornRule r = *it;
			  HornClauseDB::RuleVector &db_rules = db.getRules();
			  if(db_rules.size() == orig_rule_num + 1)
			  {
				  db_rules.pop_back();
				  db.addRule(r);
			  }
			  else
			  {
				  db.addRule(r);
			  }
			  outs() << "NEW QUERIE:\n";
			  for(auto q : db.getQueries())
			  {
				  outs() << *q << "\n";
			  }

			  ZFixedPoint<EZ3>& fp = resetFixedPoint(db);
			  boost::tribool result = fp.query();
			  if(result != UNSAT)
			  {
				  outs() << "SAT, NEED TO ADD POSITIVE DATA POINT\n";
				  //get cex
				  Expr answer = fp.getGroundSatAnswer();
				  outs() << *answer << "\n";
				  if(isOpX<TRUE>(answer))
				  {
					  outs() << "THE GROUND SAT ANSWER IS TRUE!\n";
					  continue;
				  }
				  isChanged = true;

				  Expr obj_pred = r.body()->arg(0);
				  outs() << "POS OBJ PRED: " << *obj_pred << "\n";

				  Expr cex;
				  ExprVector answer_preds;
				  get_all_pred_apps(answer, db, std::back_inserter(answer_preds));
				  for(Expr ans_pred : answer_preds)
				  {
					  if(bind::fname(obj_pred) == bind::fname(ans_pred))
					  {
						  cex = ans_pred;
					  }
				  }
				  outs() << "POS CEX IS: " << *cex << "\n";

				  //add data point to C5
				  std::list<Expr> attr_values;

				  outs() << "ANSWER ARGS:\n";
				  for(int i=0; i<bind::domainSz(bind::fname(cex)); i++)
				  {
					  Expr arg_i = cex->arg(i+1);
					  outs() << *arg_i << "\n";
					  if(bind::isBoolConst(arg_i))
					  {
						  outs() << "UNCERTAIN VALUE: " << *arg_i << "\n";
						  Expr uncertain_value = mk<FALSE>(arg_i->efac());
						  arg_i = uncertain_value;
					  }
					  else if(bind::isIntConst(arg_i))
					  {
						  outs() << "UNCERTAIN VALUE: " << *arg_i << "\n";
						  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i->efac());
						  arg_i = uncertain_value;
					  }
					  attr_values.push_back(arg_i);
				  }

				  DataPoint pos_dp(bind::fname(bind::fname(obj_pred)), attr_values);
				  addPosCex(pos_dp);
				  m_cex_list.push_back(pos_dp);
				  addDataPointToIndex(pos_dp, index);
				  outs() << "POS CEX, INDEX IS " << index << "\n";
				  index++;

				  //call C5 learner
				  //C5learn();
			  }
			  else
			  {
				  //This query is good, go to next
				  outs() << "UNSAT\n";
			  }
		  }

		  outs() << "==================================================================\n";

		  //reset the rules here !!!
		  auto &cur_rules = db.getRules();
		  cur_rules.pop_back();
		  outs() << "AFTER RESET DB IS:\n" << db;

		  outs() << "=========================== NEG START ============================\n";
		  for(auto it = m_neg_rule_set.begin(); it != m_neg_rule_set.end(); ++it)
		  {
			  HornRule r = *it;
			  Expr head = r.head();
			  HornClauseDB::RuleVector &db_rules = db.getRules();
			  if(db_rules.size() == orig_rule_num + 1)
			  {
				  db_rules.pop_back();
				  db.addRule(r);
			  }
			  else
			  {
				  db.addRule(r);
			  }
			  outs() << "NEW QUERIE:\n";
			  for(auto q : db.getQueries())
			  {
				  outs() << *q << "\n";
			  }

			  ZFixedPoint<EZ3>& fp = resetFixedPoint(db);
			  boost::tribool result = fp.query();
			  if(result != UNSAT)
			  {
				  outs() << "SAT, NEED TO ADD NEGATIVE DATA POINT\n";
				  //get cex
				  Expr answer = fp.getGroundSatAnswer();
				  outs() << *answer << "\n";
				  if(isOpX<TRUE>(answer))
				  {
					  outs() << "THE GROUND SAT ANSWER IS TRUE!\n";
					  continue;
				  }
				  isChanged = true;

				  Expr cex;
				  ExprVector answer_preds;
				  get_all_pred_apps(answer, db, std::back_inserter(answer_preds));
				  for(Expr ans_pred : answer_preds)
				  {
					  if(bind::fname(head) == bind::fname(ans_pred))
					  {
						  cex = ans_pred;
					  }
				  }
				  outs() << "NEG CEX IS: " << *cex << "\n";

				  //add data point to C5
  				  std::list<Expr> attr_values;

  				  outs() << "ANSWER ARGS:\n";
  				  for(int i=0; i<bind::domainSz(bind::fname(cex)); i++)
  				  {
  					  Expr arg_i = cex->arg(i+1);
  					  outs() << *arg_i << "\n";
  					  if(bind::isBoolConst(arg_i))
 					  {
 						  outs() << "UNCERTAIN VALUE: " << *arg_i << "\n";
 						  Expr uncertain_value = mk<FALSE>(arg_i->efac());
 						  arg_i = uncertain_value;
 					  }
 					  else if(bind::isIntConst(arg_i))
					  {
 						  outs() << "UNCERTAIN VALUE: " << *arg_i << "\n";
 						  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i->efac());
						  arg_i = uncertain_value;
					  }
  					  attr_values.push_back(arg_i);
  				  }

  				  DataPoint neg_dp(bind::fname(bind::fname(head)), attr_values);
  				  addNegCex(neg_dp);
  				  m_cex_list.push_back(neg_dp);
  				  addDataPointToIndex(neg_dp, index);
  				  outs() << "NEG CEX, INDEX IS " << index << "\n";
  				  index++;

				  //call C5 learner
				  //C5learn();
			  }
			  else
			  {
				  //This query is good, go to next
				  outs() << "UNSAT\n";
			  }
		  }

		  outs() << "==================================================================\n";

		  //reset the rules here !!!
		  auto &rules = db.getRules();
		  rules.pop_back();

		  outs() << "AFTER RESET DB IS:\n" << db;

		  outs() << "=========================== IMPL START ============================\n";
		  ZSolver<EZ3> solver(m_hm.getZContext());
		  for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it)
		  {
			  solver.reset();

			  HornRule r = *it;

			  Expr r_head = r.head();
			  Expr r_head_cand = m_candidate_model.getDef(r_head);

			  solver.assertExpr(mk<NEG>(r_head_cand));

			  Expr r_body = r.body();
			  ExprVector body_pred_apps;
			  get_all_pred_apps(r_body, db, std::back_inserter(body_pred_apps));

			  if(body_pred_apps.size() != 1)
			  {
				  continue;
			  }
			  Expr body_app = body_pred_apps[0];
			  if(bind::fname(r_head) != bind::fname(body_app))
			  {
				  continue;
			  }
			  Expr body_app_cand  = m_candidate_model.getDef(body_app);

			  solver.assertExpr(body_app_cand);

			  solver.assertExpr(extractTransitionRelation(r, db));

			  solver.toSmtLib(errs());
			  boost::tribool result = solver.solve();
			  if(result != UNSAT)
			  {
				  outs() << "SAT, NEED TO ADD IMPLICATION DATA PAIR\n";
				  isChanged = true;
				  //get cex
				  ZModel<EZ3> m = solver.getModel();
				  outs() << "(";
				  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++)
				  {
					  Expr arg_i = body_app->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  outs() << *arg_i_value << ",";
				  }
				  outs() << ") -> (";
				  for(int i=0; i<bind::domainSz(bind::fname(r_head)); i++)
				  {
					  Expr arg_i = r_head->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  outs() << *arg_i_value << ",";
				  }
				  outs() << ")\n";

				  //add impl pair
				  std::list<Expr> start_attr_values;
				  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++)
				  {
					  Expr arg_i = body_app->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  start_attr_values.push_back(arg_i_value);
				  }
				  DataPoint start_point(bind::fname(bind::fname(body_app)), start_attr_values);

				  std::list<Expr> end_attr_values;
				  for(int i=0; i<bind::domainSz(bind::fname(r_head)); i++)
				  {
					  Expr arg_i = r_head->arg(i+1);
					  Expr arg_i_value = m.eval(arg_i);
					  end_attr_values.push_back(arg_i_value);
				  }
				  DataPoint end_point(bind::fname(bind::fname(r_head)), end_attr_values);

				  if(m_pos_data_set.count(start_point) == 0 && m_neg_data_set.count(start_point) == 0 && m_impl_cex_set.count(start_point) == 0)
				  {
					  addImplCex(start_point);
					  m_cex_list.push_back(start_point);
					  addDataPointToIndex(start_point, index);
					  outs() << "IMPL CEX, INDEX IS " << index << "\n";
					  index++;
				  }
				  if(m_pos_data_set.count(end_point) == 0 && m_neg_data_set.count(end_point) == 0 && m_impl_cex_set.count(end_point) == 0)
				  {
					  addImplCex(end_point);
					  m_cex_list.push_back(end_point);
					  addDataPointToIndex(end_point, index);
					  outs() << "IMPL CEX, INDEX IS " << index << "\n";
					  index++;
				  }

				  addImplPair(std::make_pair(start_point, end_point));

				  //call C5 learner
				  //C5learn();
			  }
			  else
			  {
				  //This query is good, go to next
				  outs() << "UNSAT\n";
			  }
		  }
		  outs() << "==================================================================\n";

		  if(isChanged)
		  {
			  C5learn();
		  }
	  }

	  outs() << "FINAL INVARIANTS MAP:\n";
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr cand = m_candidate_model.getDef(fapp);
		  outs() << "REL: " << *fapp << ", CAND: " << *cand << "\n";
	  }

	  addInvarCandsToProgramSolver();
  }

  ZFixedPoint<EZ3>& ICE::resetFixedPoint(HornClauseDB &db)
  {
	  m_fp.reset (new ZFixedPoint<EZ3>(m_hm.getZContext ()));
	  ZFixedPoint<EZ3> &fp = *m_fp;
	  ZParams<EZ3> params (m_hm.getZContext ());
	  params.set (":engine", "spacer");
	  // -- disable slicing so that we can use cover
	  params.set (":xform.slice", false);
	  params.set (":use_heavy_mev", true);
	  params.set (":reset_obligation_queue", true);
	  params.set (":pdr.flexible_trace", false);
	  params.set (":xform.inline-linear", false);
	  params.set (":xform.inline-eager", false);
	  // -- disable utvpi. It is unstable.
	  params.set (":pdr.utvpi", false);
	  // -- disable propagate_variable_equivalences in tail_simplifier
	  params.set (":xform.tail_simplifier_pve", false);
	  // JN: Set to false helps with cex
	  params.set (":xform.subsumption_checker", false);
  //	  params.set (":order_children", true);
  //	  params.set (":pdr.max_num_contexts", "500");
	  fp.set (params);
	  db.loadZFixedPoint(fp, false);

	  return fp;
  }

  void ICE::constructQueries(HornClauseDB &db)
  {
	  m_pos_queries.clear();
	  m_neg_queries.clear();

	  m_pos_rule_set.clear();
	  m_neg_rule_set.clear();

	  for(Expr q : db.getQueries())
	  {
		 m_neg_queries.push_back(q);
	  }

	  //get db entry predicate
	  Expr entry_pred;
	  for(auto it = db.getRules().begin(); it!=db.getRules().end(); ++it)
	  {
		  Expr body = (*it).body();
		  if(isOpX<TRUE>(body))
		  {
			  std::ostringstream oss;
			  oss << bind::fname(bind::fname((*it).head()));
			  if(oss.str() == std::string("verifier.error"))
			  {
				  continue;
			  }
			  entry_pred = (*it).head();
		  }
	  }
	  outs() << "ENTRY IS: " << *entry_pred << "\n";

	  assert(m_neg_queries.size() == 1);

	  for(Expr rel : db.getRelations())
	  {
		  ExprVector args;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  //Expr arg_i = bind::bvar(i, arg_i_type);
			  args.push_back(arg_i);
		  }
		  Expr rel_app = bind::fapp(rel, args);
		  Expr cand_app = m_candidate_model.getDef(rel_app);

		  //construct pos queries
		  Expr pos_qry = mk<AND>(rel_app, mk<NEG>(cand_app));
		  m_pos_queries.push_back(pos_qry);

		  //construct pos rules
		  Expr error_split = db.getQueries()[0];
		  outs() << "ERROR PRED: " << *error_split << "\n";
		  HornRule pos_rule(args, error_split, mk<AND>(rel_app, mk<NEG>(cand_app)));
		  m_pos_rule_set.insert(pos_rule);

		  //construct neg rules
		  ExprVector vars;
		  vars.insert(vars.end(), args.begin(), args.end());
		  for(int i=0; i<bind::domainSz(bind::fname(entry_pred)); i++)
		  {
			  Expr entry_arg_i = entry_pred->arg(i+1);
			  vars.push_back(entry_arg_i);
		  }
		  if(rel == bind::fname(entry_pred))
		  {
			  HornRule neg_rule(vars, rel_app, cand_app);
			  m_neg_rule_set.insert(neg_rule);
		  }
		  else
		  {
			  HornRule neg_rule(vars, rel_app, mk<AND>(entry_pred, cand_app));
			  m_neg_rule_set.insert(neg_rule);
		  }
	  }
  }

}
