#!/usr/bin/env python
import z3
import z3core
import stats
import tempfile
import atexit
from z3_utils import *
from LogManager import LoggingManager
import os,subprocess,sys
import shutil
import term.stats as stats
import threading
import signal

root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose=False
bench=False
running_process = None

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


out_message = ("""
FUNCTION NAME = %s
RESULT = %s
SET OF INVARIANTS = %s
CONSISTENT FLAG(S)  = %s
INCONSISTENT FLAG(S) = %s
""")

def stat (key, val): stats.put (key, val)

class Inc(object):
    def __init__(self, args):

        verbose = args.verbose
        self.args = args
        self.ctx = z3.Context ()
        self.fp = z3.Fixedpoint (ctx=self.ctx)
        self.preds = []
        self.ee_idx = [] #entry/exit vars
        self.feasible_flag = [] # keep track of the  feasible path
        self.non_feasible_flag = [] # keep track of the infesible path
        return

    def solve(self, smt2_file):
        """
        Start solving
        """
        self.fp.set (engine='spacer')
        if self.args.stat:
            self.fp.set('print_statistics',True)
        if self.args.z3_verbose:
            z3.set_option (verbose=1)
        self.fp.set('use_heavy_mev',True)
        self.fp.set('pdr.flexible_trace',True)
        self.fp.set('reset_obligation_queue',False)
        self.fp.set('spacer.elim_aux',False)
        if self.args.utvpi: self.fp.set('pdr.utvpi', False)
        if not self.args.pp:
            self.fp.set ('xform.slice', False)
            self.fp.set ('xform.inline_linear',False)
            self.fp.set ('xform.inline_eager',False)
        with stats.timer ('Parse'):
            queries = self.fp.parse_file (smt2_file)
            stats.stop('Parse')
            self.preds = get_preds(self.fp)
            n_function = len(queries)
            stat("Function_Numbers", n_function)
            # TODO: Put them in a multithreading function
            all_results = ""
            for q in queries:
                if z3.is_quantifier(q):
                    decl = q.body().decl()
                    function_name = str(decl).split("@")[0]
                    try:
                        out = self.checkFeasibility(q, function_name)
                        all_results += out + "\n-----------------------\n"
                    except Exception as e:
                        print "Solving " + function_name
                else:
                    function_name = str(q.decl()).split("@")[0]
                    out = out_message % (function_name, "CONSISTENT", "", "Trivial", "")
                    all_results += bcolors.OKGREEN + out + bcolors.ENDC
            print "\n\t ========= SEAHORN INCONSISTENCY RESULTS ========"
            print all_results


    def checkFeasibility(self, expr_query, function_name):
        done = False
        rounds = 0 # counter for feasibility check
        self.ee_idx = self.ee_vars(expr_query)
        if verbose: print "EE VARS INDEX:", self.ee_idx
        out = ""
        while not done:
            with stats.timer ('Query'):
                res = self.fp.query (expr_query) #if round == 0 else self.fp.query_from_lvl(12,expr_query)
                if res == z3.sat:
                    msg = "ENTRY -> EXIT is FEASIBLE" if rounds==0 else "STILL FEASIBLE: Continue checking ..."
                    if verbose: print "( " + function_name + " ) " + msg
                    expr_query, path = self.cex(expr_query)
                    self.feasible_flag = self.ee_idx
                    rounds += 1
                    if expr_query is None:
                        result = "[%s], Feasible" % function_name
                        stat('Result', result)
                        stat('Rounds', str(rounds))
                        out += out_message % (function_name, "CONSISTENT", "", str(self.feasible_flag),  str(self.non_feasible_flag))
                        out = bcolors.OKGREEN + out + bcolors.ENDC
                        done = True
                elif res == z3.unsat:
                    result = "[%s], Infeasible" % function_name
                    stat('Result', result)
                    stat('Rounds', str(rounds))
                    msg = "EXIT is not FEASIBLE" if rounds==0 else "INFEASIBLE BLOCK FOUND"
                    if rounds == 0:
                        self.feasible_flag.append(self.ee_idx[0])
                        self.non_feasible_flag.append(self.ee_idx[1])
                    if verbose: print " ( " + function_name + " ) " + msg
                    inv =  "\n"
                    for p in self.preds:
                        lemmas = fp_get_cover_delta (self.fp, p)
                        inv += "\tBasic Block: " + str(p.decl())
                        inv += "\n\tInvariant: " + str(lemmas)
                        inv += "\n\t-----------\n"
                    inv_info = inv if self.args.inv else "(set --inv to get invariants info)"
                    out += out_message % (function_name, "INCONSISTENT", inv_info, str(self.feasible_flag),  str(self.non_feasible_flag))
                    out = bcolors.FAIL + out + bcolors.ENDC
                    done = True
                stats.stop('Query')
            # debugging purpose
            if self.args.stop != None:
                self.args.stop -=1
                done = self.args.stop==0
        return out

    def cex(self, qr):
        """
        It returns
          * new horn query if we have to continue checking for feasibility
          * None if we are done, plus return the path
        """
        if verbose: print "Inspecting the CEX ... "
        raw_cex = self.fp.get_ground_sat_answer()
        ground_sat = get_conjuncts(raw_cex)
        if verbose: print "RAW CEX:", ground_sat
        fpred = ground_sat[0] if len(ground_sat[0].children()) != 0 else ground_sat[1] # inspecting the first predicate
        var_flags = self.getListFlags(fpred)
        flags_number = len(var_flags) + 1 # TODO Jorge
        true_idxs, false_idxs = self.tfFlags(fpred, flags_number)
        t_flags = [t for t in true_idxs if t not in self.ee_idx] # filter  entry/exit flags
        f_flags = [t for t in false_idxs if t not in self.ee_idx] # filter entry/exit flags
        self.feasible_flag +=  t_flags
        self.non_feasible_flag = f_flags
        if verbose: print "TRUE FLAGS:" + str(t_flags) ,  "\nFALSE FLAGS:" + str(f_flags)
        if f_flags == []:
            if verbose: print "No failing flags ..."
            return None, ground_sat
        else:
            new_query = self.mkNewQuery(qr, fpred, t_flags, f_flags)
            return new_query, ground_sat

    def ee_vars(self, qr):
        """
        Given a query get exit vars
        """
        body = qr.body()
        ch = body.children()
        i = 0
        true_vars = []
        for c in ch:
            if z3.is_true(c):
                true_vars.append(i)
            i+=1
        return true_vars


    def mkNewQuery(self, qr, fpred, t_flags, f_flags):
        """
        Create a new query by adding
         * qr old query
         * fpred failing predicate
         * idxs list of failing predicate
        """
        print "Creating a new query ..."
        body = qr.body()
        pred = None
        for p in self.preds:
            if fpred.decl().eq(p.decl()): pred = p
        pred_vars = pred.children()
        false_vars = self.getVars(f_flags, pred_vars, qr)
        true_vars = self.getVars(t_flags, pred_vars, qr)
        not_vars = [z3.Not(ix) for ix in false_vars]
        exist_vars, body = stripQuantifierBlock(qr)
        true_false_vars = not_vars + true_vars + [qr.ctx]
        new_vars_conjunct = z3.Not(z3.And(*true_false_vars))
        and_predicate = z3.And(*[body,new_vars_conjunct,qr.ctx])
        if verbose: print "New Conjunct:", and_predicate
        new_exist_vars = self.existVars(exist_vars, true_false_vars)
        new_query = z3.Exists(new_exist_vars,and_predicate)
        if verbose: print "NEW Query:\n", new_query
        return new_query

    def getVars(self, idxs, pred_vars, qr):
        """
        given a list of indexes return var names
        """
        vars = list()
        for idx in idxs:
            v = pred_vars[idx]
            if z3.is_true(v):
                new_v = z3.Bool("__r"+str(idx)+"_0", qr.ctx)
                vars.append(new_v)
            else:
                vars.append(v)
        return vars


    def existVars(self, v1, v2):
        """
        create a list of variables to be bound
        """
        v1_str = [str(v) for v in v1]
        v2_filtered = list()
        for v in v2:
            if z3.is_not(v):
                v2_filtered.append(v.children()[0])
            elif z3.is_app(v) and not z3.is_not(v):
                v2_filtered.append(v)
        for v in v2_filtered:
            if str(v) not in v1_str : v1.append(v)
        return v1


    def tfFlags(self, pred, flags_len):
        """
        return two lists, one for true and one false flags
        """
        false_idxs = list()
        true_idxs = list ()
        if verbose: print "Get list of failing flags from : ", pred
        ch = pred.children()
        i=0
        for val in ch[0:flags_len]:
            if z3.is_false(val):
                false_idxs.append(i)
                i+=1
            elif z3.is_true(val):
                true_idxs.append(i)
                i+=1
            else: i+=1
        return true_idxs, false_idxs

    def getListFlags(self, pred):
        """
        Return a list of the flags variable
        """
        flags = []
        for p in self.preds:
            if str(p.decl()) == str(pred.decl()):
                for var in p.children():
                    p_split = str(var).split('_')
                    if "__" in str(var):
                        flags.append(var)
        return flags





def fp_add_cover (fp, pred, lemma, level=-1):
    # no trivial lemmas
    if z3.is_true (lemma): return

    assert (z3.is_app (pred))

    sub = []
    for i in range (0, pred.num_args ()):
        arg = pred.arg (i)
        sub.append ((arg,
                     z3.Var (i, arg.decl ().range ())))

    tlemma = z3.substitute (lemma, sub)
    if verbose:
        print "Lemma for ", pred.decl (), ": ", tlemma
    fp.add_cover (level, pred.decl (), tlemma)


def fp_get_cover_delta (fp, pred, level=-1):
    sub = []
    for i in range (0, pred.num_args ()):
        sub.append (pred.arg (i))
    lemma = fp.get_cover_delta (level, pred.decl ())
    if z3core.Z3_get_bool_value (fp.ctx.ctx, lemma.as_ast ()) != z3.unsat:
        lemma = z3.substitute_vars (lemma, *sub)
    return lemma


def get_preds (fp):
    seen = set ()
    res = list ()
    for rule in fp.get_rules ():
        pred = rule
        # A rule is of the form
        # FORALL? (BODY IMPLIES)? PRED
        if z3.is_quantifier (pred): pred = pred.body ()
        if is_implies (pred): pred = pred.arg (1)

        decl = pred.decl ()
        assert is_uninterpreted (decl)
        if z3key (decl) in seen: continue
        seen.add (z3key (decl))

        # if the rule contains a universal quantifier, replace
        # variables by properly named constants
        if z3.is_quantifier (rule):
            sub = [ z3.Const (bound_var_name (rule, i),
                              bound_var_sort (rule, i))
                    for i in range (0, rule.num_vars ()) ]
            pred = substitute_vars (pred, *sub)
        res.append (pred)
    return res




def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='Feasibility check with SeaHorn')

    p.add_argument ('file', metavar='BENCHMARK', help='Benchmark file (by default in C)')
    p.add_argument ('--track',
                    help='Track registers, pointers, and memory',
                    choices=['reg', 'ptr', 'mem'], default='mem')
    p.add_argument ('--smt2', dest='is_smt2',
                    help='Benchmark file is in smt2 format',
                    action='store_true', default=False)
    p.add_argument ('--bc', dest='bc',
                    help='LLVM bitecode format',
                    action='store_true', default=False)
    p.add_argument ('--entry', metavar='FUNCNAME', dest='entry_point',
                    help='Entry point to the program (--seapp must be enabled)', default=None)
    p.add_argument ('--seapp', dest='seapp',
                    help='Enable Seahorn preprocessor',
                    action='store_true', default=False)
    p.add_argument ('-O', type=int, dest='opt_level', metavar='INT',
                     help='Optimization level L:[0,1,2,3]', default=0)
    p.add_argument ('--pp',
                    help='Enable default pre-processing in the solver',
                    action='store_true', default=False)
    p.add_argument ("--save-temps", dest="save_temps",
                       help="Do not delete temporary files",
                       action="store_true",
                       default=False)
    p.add_argument ("--temp-dir", dest="temp_dir", metavar='DIR',
                       help="Temporary directory",
                       default=None)
    p.add_argument ('--stop', help='stop after n iterations', dest="stop",
                    default=None, type=int)
    p.add_argument ('--all', help='assert all failing flags', dest="all",
                    default=False,action='store_true')
    p.add_argument ('--stat', help='Print statistics', dest="stat",
                    default=False, action='store_true')
    p.add_argument ('--verbose', help='Verbose', action='store_true',
                    default=False, dest="verbose")
    p.add_argument ('--spacer_verbose', help='Spacer Verbose', action='store_true',
                    default=False, dest="z3_verbose")
    p.add_argument ('--bench', help='Output Benchmarking Info', action='store_true',
                    default=False, dest="bench")
    p.add_argument ('--inv', help='Outpu Invariants', action='store_true',
                    default=False, dest="inv")
    p.add_argument ('--no_dl', help='Disable Difference Logic (UTVPI) in SPACER', action='store_true',
                    default=False, dest="utvpi")
    pars = p.parse_args (argv)
    global verbose
    verbose = pars.verbose
    global bench
    bench = pars.bench
    return pars




def main (argv):
    args = parseArgs (argv[1:])

    in_name = args.file
    if not args.is_smt2:
        workdir = createWorkDir (args.temp_dir, args.save_temps)

        if not args.bc:
            bc_out = defBCName (in_name, workdir)
            assert bc_out != in_name
            extra_args = []
            clang (in_name, bc_out, arch=32, extra_args=extra_args)
            in_name = bc_out

        if args.seapp:
            pp_out = defPPName (in_name, workdir)
            assert pp_out != in_name
            seapp (in_name, pp_out, arch=32, args=args)
            in_name = pp_out

        if args.opt_level > 0:
            opt_out = defOPTName (in_name, args.opt_level, workdir)
            llvmOpt (in_name, opt_out, args.opt_level)
            in_name = opt_out

        smt_out = defSMTName(in_name, workdir)
        seahorn_args = []
        seahorn_args.extend (['-horn-sem-lvl={0}'.format (args.track)])

        seahorn (in_name, smt_out, seahorn_args)
        in_name = smt_out

    stat ('Result', 'UNKNOWN')
    feas = Feas(args)
    feas.solve(in_name)


if __name__ == '__main__':
    res = None
    try:
        main (sys.argv)
    except Exception as e:
        print str(e)
    finally:
        if bench: stats.brunch_print ()
    sys.exit (res)
