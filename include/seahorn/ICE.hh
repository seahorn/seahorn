#ifndef ICE__HH_
#define ICE__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/GuessCandidates.hh"
#include "seahorn/HornDbModel.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>

#include <algorithm>

namespace seahorn
{
  using namespace llvm;

  class ICEPass : public llvm::ModulePass
  {
  public:
    static char ID;

    ICEPass() : ModulePass(ID) {}
    virtual ~ICEPass() {}

    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "ICE";}
  };

  class DataPoint
  {
	  Expr m_pred;
	  std::list<Expr> m_values;
  public:
	  DataPoint() {}
	  DataPoint(Expr pred, std::list<Expr>& attr_values) : m_pred(pred), m_values(attr_values) {}
	  virtual ~DataPoint() {}
	  Expr getPredName() {return m_pred;}
	  std::list<Expr>& getAttrValues() {return m_values;}

	  size_t hash () const
	  {
		size_t res = expr::hash_value (m_pred);
		boost::hash_combine (res, boost::hash_range (m_values.begin (),
													 m_values.end ()));
		return res;
	  }

	  bool operator==(const DataPoint & other) const
	  { return hash() == other.hash ();}

	  bool operator<(const DataPoint & other) const
	  { return hash() < other.hash ();}
  };

  class ICE
  {
  public:
	  ICE(HornifyModule &hm) : m_hm(hm)  {}
	  virtual ~ICE() {m_fp.reset (nullptr);}
  private:
	  HornifyModule &m_hm;
	  HornDbModel m_candidate_model;

	  std::unique_ptr<ufo::ZFixedPoint <ufo::EZ3> >  m_fp;

	  std::string m_C5filename;

	  ExprMap m_attr_name_to_expr_map;
	  ExprMap m_rel_to_c5_rel_name_map;
	  ExprMap m_c5_rel_name_to_rel_map;

	  std::set<HornRule> m_pos_rule_set;
	  std::set<HornRule> m_neg_rule_set;

	  Expr m_pos_query;
	  ExprVector m_orig_queries;

	  std::set<DataPoint> m_pos_data_set;
	  std::set<DataPoint> m_neg_data_set;
	  std::set<DataPoint> m_impl_cex_set;
	  std::set<std::pair<DataPoint, DataPoint>> m_impl_pair_set;

	  std::map<DataPoint, int> m_data_point_to_index_map;
	  std::vector<DataPoint> m_cex_list;

  public:
	  void setupC5();
	  void C5learn();
	  std::string outputDataPoint(DataPoint p);

  public:
      HornifyModule& getHornifyModule() {return m_hm;}
      HornDbModel& getCandidateModel() {return m_candidate_model;}

      std::set<HornRule>& getPosRuleSet() {return m_pos_rule_set;}
      std::set<HornRule>& getNegRuleSet() {return m_neg_rule_set;}

  public:
      void runICE();

      void guessCandidates(HornClauseDB &db);

      //Add ICE invs to default solver
      void addInvarCandsToProgramSolver();

      void genInitialCandidates(HornClauseDB &db);
      void generateC5DataAndImplicationFiles();

      void constructPosAndNegRules(HornClauseDB &db);

      void addPosCex(DataPoint dp) {m_pos_data_set.insert(dp);}
      void addNegCex(DataPoint dp) {m_neg_data_set.insert(dp);}
      void addImplCex(DataPoint dp) {m_impl_cex_set.insert(dp);}
      void addImplPair(std::pair<DataPoint, DataPoint> pair) {m_impl_pair_set.insert(pair);}

      void addDataPointToIndex(DataPoint dp, int index) {m_data_point_to_index_map.insert(std::make_pair(dp, index));}

      void convertPtreeToInvCandidate(boost::property_tree::ptree pt);
      std::list<std::list<Expr>> constructFormula(std::list<Expr> stack, boost::property_tree::ptree sub_pt);

      ZFixedPoint<EZ3>& resetFixedPoint(HornClauseDB &db);

      void setPosQuery();

      void recordPosCexs(HornClauseDB &db, bool &isChanged, int &index);
      void recordNegCexs(HornClauseDB &db, bool &isChanged, int &index);
      void recordImplPairs(HornClauseDB &db, bool &isChanged, int &index);

      Expr plusAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name);
      Expr minusAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name);
  };
}

#endif /* HOUDNINI__HH_ */
