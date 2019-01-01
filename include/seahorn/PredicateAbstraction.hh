#ifndef PREDICATE_ABSTRACTION__HH_
#define PREDICATE_ABSTRACTION__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornDbModel.hh"
#include "seahorn/HornModelConverter.hh"
#include "seahorn/GuessCandidates.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

namespace seahorn
{
	using namespace llvm;

	class PredAbsHornModelConverter : public HornModelConverter
	{
	private:
		std::map<Expr, ExprMap> m_relToBoolToTermMap;
		std::map<Expr, Expr> m_newToOldPredMap;
		HornClauseDB* m_abs_db;

		std::map<Expr, ExprMap>& getRelToBoolToTermMap() {return m_relToBoolToTermMap;}
	public:
		PredAbsHornModelConverter() {}
		virtual ~PredAbsHornModelConverter() {}
		bool convert (HornDbModel &in, HornDbModel &out);

		void addRelToBoolToTerm(Expr rel, ExprMap &boolToTermMap) {m_relToBoolToTermMap.insert(std::make_pair(rel, boolToTermMap));}
		void setNewToOldPredMap(std::map<Expr, Expr> &newToOldMap) {m_newToOldPredMap = newToOldMap;}
		void setAbsDB(HornClauseDB &db) {m_abs_db = &db;}
	};

	class PredicateAbstractionAnalysis
	{
	private:
	    std::map<Expr, Expr> m_oldToNewPredMap;
	    std::map<Expr, Expr> m_newToOldPredMap;
	    std::map<Expr, ExprVector> m_currentCandidates;

	    HornifyModule& m_hm;

	public:
	    PredicateAbstractionAnalysis(HornifyModule &hm) : m_hm(hm) {}
	    ~PredicateAbstractionAnalysis() {}

		void guessCandidate(HornClauseDB &db);

		Expr applyArgsToBvars(Expr cand, Expr fapp, std::map<Expr, ExprVector> currentCandidates);
		ExprMap getBvarsToArgsMap(Expr fapp, std::map<Expr, ExprVector> currentCandidates);

		void generateAbstractDB(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractRelations(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractRules(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter);
		void generateAbstractQueries(HornClauseDB &db, HornClauseDB &new_DB);
	};

	class PredicateAbstraction : public llvm::ModulePass
	{
	public:
	    static char ID;

	    PredicateAbstraction() : ModulePass(ID) {}
	    virtual ~PredicateAbstraction() {}
	    void releaseMemory () {m_fp.reset (nullptr);}
	    virtual bool runOnModule (Module &M);
	    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
	    virtual StringRef getPassName () const {return "PredicateAbstraction";}

	    ufo::ZFixedPoint<ufo::EZ3>& getZFixedPoint () {return *m_fp;}

	    void printInvars(Function &F, HornDbModel &origModel);
	    void printInvars(Module &M, HornDbModel &origModel);
	private:
	    std::unique_ptr<ufo::ZFixedPoint <ufo::EZ3> >  m_fp;
	};
}

#endif
