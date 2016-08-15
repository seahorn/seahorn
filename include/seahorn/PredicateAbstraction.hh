#ifndef PREDICATE_ABSTRACTION__HH_
#define PREDICATE_ABSTRACTION__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

namespace seahorn
{
	using namespace llvm;

	class HornDbModel
	{
	private:
		ExprMap relToDefMap;
		std::map<Expr, ExprVector> currentCandidates;
	public:
		HornDbModel() {}
		void initModelFromFP(HornClauseDB &db, ZFixedPoint<EZ3> &fp);
		void addDef(Expr fapp, Expr def);
		Expr getDef(Expr fapp);
		HornDbModel(ExprMap model) : relToDefMap(model) {}
		virtual ~HornDbModel(){}
		void setCurrentCandidates(std::map<Expr, ExprVector> currentCandidates) { this->currentCandidates = currentCandidates; }
//		ExprMap& getRelToSolutionMap() {return relToDefMap;}
//		void setRelToSolutionMap(ExprMap map) {relToDefMap = map;}
	};

	class HornModelConverter
	{
	public:
		// converts a model from one database to another. returns false on failure.
		virtual bool convert (HornDbModel &in, HornDbModel &out) = 0;
	};

	class PredAbsHornModelConverter : public HornModelConverter
	{
	private:
		std::map<Expr, ExprMap> relToBoolToTermMap;
		std::map<Expr, Expr> newToOldPredMap;
		HornClauseDB* abs_db;
	public:
		PredAbsHornModelConverter() {}
		bool convert (HornDbModel &in, HornDbModel &out);
		std::map<Expr, ExprMap>& getRelToBoolToTermMap() {return relToBoolToTermMap;}
		void setNewToOldPredMap(std::map<Expr, Expr> &newToOldMap) {newToOldPredMap = newToOldMap;}
		void setAbsDB(HornClauseDB &db) {abs_db = &db;}
	};

	class PredicateAbstractionAnalysis
	{
	private:
	    std::map<Expr, Expr> oldToNewPredMap;
	    std::map<Expr, Expr> newToOldPredMap;
	    std::map<Expr, ExprVector> currentCandidates;

	    std::unique_ptr<ufo::ZFixedPoint <ufo::EZ3> >  m_fp;
	    HornifyModule& m_hm;

	public:
	    PredicateAbstractionAnalysis(HornifyModule &hm) : m_hm(hm) {}
	    ~PredicateAbstractionAnalysis() {m_fp.reset (nullptr);}

	    ufo::ZFixedPoint<ufo::EZ3>& getZFixedPoint () {return *m_fp;}

	    void runAnalysis();
		void guessCandidate(HornClauseDB &db);
		ExprVector relToCand(Expr fdecl);
		HornClauseDB generateAbstractDB(HornClauseDB &db, PredAbsHornModelConverter &converter);
		void generateAbstractRelations(HornClauseDB &db, HornClauseDB &new_DB);
		void generateAbstractRules(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractQueries(HornClauseDB &db, HornClauseDB &new_DB);
		void printInvars(HornClauseDB &db, HornDbModel &origModel);
	};

	class PredicateAbstraction : public llvm::ModulePass
	{
	public:
	    static char ID;

	    PredicateAbstraction() : ModulePass(ID) {}
	    virtual ~PredicateAbstraction() {}
	    virtual bool runOnModule (Module &M);
	    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
	    virtual const char* getPassName () const {return "PredicateAbstraction";}
	};

	class HornDbUtils
	{
	public:
		static Expr applyArgsToBvars(Expr cand, Expr fapp, std::map<Expr, ExprVector> currentCandidates);
		static ExprMap getBvarsToArgsMap(Expr fapp, std::map<Expr, ExprVector> currentCandidates);
		static Expr extractTransitionRelation(HornRule r, HornClauseDB &db);

		template<typename OutputIterator>
		static void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out)
		{filter (e, IsPredApp(db), out);}

		template<typename OutputIterator>
		static void get_all_bvars (Expr e, OutputIterator out)
		{filter (e, IsBVar(), out);}

		template<typename OutputIterator>
		static void get_all_integers(Expr e, OutputIterator out)
		{filter (e, IsInteger(), out);}

		template<typename OutputIterator>
		static void get_all_booleans(Expr e, OutputIterator out)
		{filter (e, IsBoolean(), out);}

		static bool hasBvarInRule(HornRule r, HornClauseDB &db, std::map<Expr, ExprVector> currentCandidates);

		struct IsPredApp : public std::unary_function<Expr, bool>
		{
			 HornClauseDB &m_db;
			 IsPredApp (HornClauseDB &db) : m_db (db) {}

			 bool operator() (Expr e)
			 {return bind::isFapp (e) && m_db.hasRelation (bind::fname(e));}
		};

		struct IsBVar : public std::unary_function<Expr, bool>
		{
			 IsBVar () {}
			 bool operator() (Expr e)
			 {return bind::isBVar (e);}
		};

		struct IsInteger : public std::unary_function<Expr, bool>
		{
			IsInteger() {}
			bool operator() (Expr e)
			{return bind::isIntConst (e);}
		};

		struct IsBoolean : public std::unary_function<Expr, bool>
		{
			IsBoolean() {}
			bool operator() (Expr e)
			{return bind::isBoolConst (e);}
		};
	};
}

#endif
