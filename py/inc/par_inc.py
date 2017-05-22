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
import stats
import threading
from multiprocessing import Process, Pool
import multiprocessing
import logging
import ntpath


root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose=False
bench=False
debug_cex= False

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
INC_STAT|RESULT|%s
SET OF INVARIANTS = %s
INC_STAT|CONSISTENT_FLAGS|%s
INC_STAT|INCONSISTENT_FLAGS|%s
INC_STAT|ROUNDS|%s
INC_STAT|QUERY_TIME|%s
""")


class Feasibility(object):
    def __init__(self, args, smt2_file):
        log = 3 if verbose else 0
        self.log = LoggingManager.get_logger(__name__,log)
        self.smt2_file = smt2_file
        self.args = args
        self.ctx = z3.Context()
        self.fp = z3.Fixedpoint(ctx=self.ctx)
        self.ee_idx = list() #entry/exit vars
        self.feasible_flag = set() # keep track of the  feasible path
        self.non_feasible_flag = set() # keep track of the infesible path
        self.timeout = args.timeout # timeout per function
        self.flags = None
        self.preds = None
        self.function_name = None
        self.query_times = list()


    def run(self, query_index):
        self.fp.set (engine='spacer')
        if self.args.stat:
            self.fp.set('print_statistics',True)
        if self.args.z3_verbose:
            z3.set_option (verbose=1)
        if self.args.utvpi: self.fp.set('pdr.utvpi', False)
        self.fp.set('use_heavy_mev',True)
        self.fp.set('pdr.flexible_trace',True)
        self.fp.set('reset_obligation_queue',False)
        self.fp.set('spacer.elim_aux',False)
        if not self.args.pp:
            self.log.info("No pre-processing")
            self.fp.set ('xform.slice', False)
            self.fp.set ('xform.inline_linear',False)
            self.fp.set ('xform.inline_eager',False)
        queries = self.fp.parse_file (self.smt2_file)
        self.preds = get_preds(self.fp)
        out = ""
        query = queries[query_index]
        if z3.is_quantifier(query):
            decl = query.body().decl()
            self.function_name = str(decl).split("@")[0]
            out = self.checkFeas(query)
            return out
        else:
            function_name = str(query.decl()).split("@")[0]
            out = out_message % (function_name, "FEASIBLE", "", "", "", "", "")
            out = bcolors.OKGREEN + out + bcolors.ENDC
            return out


    def feasOut(self):
        feas = list(self.feasible_flag)
        infeas = []
        for x in self.non_feasible_flag:
            if x not in feas:
                infeas.append(x)
        return feas, infeas


    def checkFeas(self, expr_query):
        done = False # flag to stop the feasibility checking
        rounds = 1 # counter for feasibility check
        self.ee_idx = self.ee_vars(expr_query) #entr/exit vars
        self.log.info("EE VARS INDEX ..." + str(self.ee_idx))
        out = ""
        function_name = self.function_name
        while not done:
            with stats.timer ('Query'):
                #if round == 0 else self.fp.query_from_lvl(12, expr_query)
                res = self.fp.query (expr_query)
                stats.stop('Query')
                self.query_times.append(str(stats.get('Query')))
                if bench: print "Query | Round [" + str(rounds) + "] | time  [" + str(stats.get('Query')) + " ms]"
                if res == z3.sat:
                    msg = "ENTRY -> EXIT is FEASIBLE" if rounds==1 else "STILL FEASIBLE: Continue checking ..."
                    self.log.info("( " + function_name + " ) " + msg)
                    self.feasible_flag |= set(self.ee_idx)
                    expr_query, path = self.cex(expr_query)
                    rounds += 1
                    if expr_query is None:
                        feas = list(self.feasible_flag)
                        infeas = ";".join([str(x) for x in list(self.non_feasible_flag)])
                        q_times = [float(x) for x in self.query_times]
                        q_average = sum(q_times) / len(q_times)
                        out += out_message % (function_name, "FEASIBLE", "", str(feas),  infeas, str(rounds), str(q_average))
                        out = bcolors.OKGREEN + out + bcolors.ENDC
                        done = True
                elif res == z3.unsat:
                    inv =  "\n-----------\n"
                    for p in self.preds:
                        lemmas = fp_get_cover_delta (self.fp, p)
                        inv += "\tBasic Block: " + str(p.decl())
                        inv += "\n\tInvariant: " + str(lemmas)
                        inv += "\n-----------\n"
                    inv_info = inv if self.args.inv else "(set --inv to get invariants info)"

                    if len(list(self.feasible_flag)) == self.flags:
                        self.log.info(" ( " + function_name + " ) FEASIBLE")
                        feas = list(self.feasible_flag)
                        q_times = [float(x) for x in self.query_times]
                        q_average = sum(q_times) / len(q_times)
                        out += out_message % (function_name, "FEASIBLE", inv_info, str(feas), "", str(rounds), str(q_average))
                        out = bcolors.OKGREEN + out + bcolors.ENDC
                    else:
                        msg = "EXIT is not FEASIBLE" if rounds==1 else "INFEASIBLE BLOCK FOUND"
                        self.feasOut()
                        if rounds == 1:
                            self.feasible_flag.add(self.ee_idx[0])
                            self.non_feasible_flag.add(self.ee_idx[1])
                        self.log.info(" ( " + function_name + " ) " + msg)
                        feas, infeas = self.feasOut()
                        q_times = [float(x) for x in self.query_times]
                        q_average = sum(q_times) / len(q_times)
                        infeas_str = ";".join([str(x) for x in infeas])
                        out += out_message % (function_name, "INFEASIBLE", inv_info, str(feas), infeas_str, str(rounds), str(q_average))
                        out = bcolors.FAIL + out + bcolors.ENDC
                    done = True
                else:
                    out += out_message % (function_name, "UNKNOWN", "", "", "", "", "")
                    done = True
        return out

    def cex(self, qr):
        """
        It returns
          * new horn query if we have to continue checking for feasibility
          * None if we are done, plus return the path
        """
        self.log.info("Inspecting the CEX ... ")
        raw_cex = self.fp.get_ground_sat_answer()
        ground_sat = get_conjuncts(raw_cex)
        if debug_cex: print "RAW CEX:", ground_sat
        fpred = ground_sat[0] if len(ground_sat[0].children()) != 0 else ground_sat[1] # inspecting the first predicate
        var_flags = self.getListFlags(fpred)
        self.flags = len(var_flags) + 1 # TODO Jorge
        true_idxs, false_idxs = self.tfFlags(fpred, self.flags)
        t_flags = [t for t in true_idxs if t not in self.ee_idx] # filter  entry/exit flags
        f_flags = [t for t in false_idxs if t not in self.ee_idx] # filter entry/exit flags
        self.feasible_flag |= set(t_flags)
        self.non_feasible_flag = set(f_flags)
        self.log.info("TRUE FLAGS ... " + str(t_flags) +  "\t FALSE FLAGS ... "  + str(f_flags))
        if f_flags == []:
            self.log.info("No failing flags ...")
            return None, ground_sat
        else:
            new_query = self.mkNewQuery(qr, fpred, t_flags, f_flags)
            return new_query, ground_sat

    def ee_vars(self, qr):
        """
        Given a query get entry and exit vars
        """
        body = qr.body()
        ch = body.children()
        i = 0
        true_vars = list()
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
        self.log.info("Creating a new query ...")
        body = qr.body()
        pred = None
        for p in self.preds:
            if fpred.decl().eq(p.decl()): pred = p
        pred_vars = pred.children()
        false_vars = self.mkVars(f_flags, qr)
        true_vars = self.mkVars(t_flags, qr)
        not_vars = [z3.Not(ix) for ix in false_vars]
        exist_vars, body = stripQuantifierBlock(qr)
        true_false_vars = not_vars + true_vars + [qr.ctx]
        new_vars_conjunct = z3.Not(z3.And(*true_false_vars)) if len(not_vars + true_vars) >= 2 else z3.Not(*true_false_vars)
        and_predicate = z3.And(*[body,new_vars_conjunct,qr.ctx])
        if debug_cex: print "New Conjunct:", and_predicate
        new_exist_vars = self.existVars(exist_vars, true_false_vars)
        new_query = z3.Exists(new_exist_vars,and_predicate)
        if debug_cex: print "NEW Query:\n", new_query

        #print "NEW Query:\n", new_query
        return new_query

    def mkVars(self, idxs, qr):
        """
        given a list of indexes return var names
        """
        vars = list()
        for idx in idxs:
            new_v = z3.Bool("__r"+str(idx)+"_0", qr.ctx)
            vars.append(new_v)
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
        if debug_cex: print "Get list of failing flags from : ", pred
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



def jobStarter(args, query_index, smt2_file):
    """
    Spawn jobs
    """
    job = Feasibility(args, smt2_file)
    out = job.run(query_index)
    return out


def checkFeas(args, query_index, smt2_file):
    """
    Start feasibility jobs
    """
    job = Feasibility(args, smt2_file)
    out = job.run(query_index)
    print out


class JobsSpanner(object):
    """
    Class to start all the inconsistency jobs and start
    callbacks for results
    """
    def __init__(self, args):
        print "\n\t =========  SEAHORN INCONSISTENCY CHECKS   ========"
        global verbose
        verbose = args.inc_verbose
        global bench
        bench = args.bench
        global debug_cex
        debug_cex = args.debug_cex
        log = 3 if verbose else 0
        self.log = LoggingManager.get_logger(__name__,log)
        self.args = args
        self.all_result = ""
        return

    def onReturn(self, out):
        self.all_result += out + "\n-----------------------\n"


    def getFunctionName(self, query):
        if z3.is_quantifier(query):
            decl = query.body().decl()
            return str(decl).split("@")[0]
        else:
            return str(query.decl()).split("@")[0]


    def singleRun(self, smt2_file):
        """
        Single run
        """
        ctx = z3.Context ()
        fp = z3.Fixedpoint (ctx=ctx)
        with stats.timer ('Parse'):
            self.log.info('Parsing  ... ' + str(smt2_file))
            queries = fp.parse_file (smt2_file)
            stats.stop('Parse')
            self.log.info("Parsing time ... " + str(stats.get('Parse')) + " ms")
            n_function = len(queries)
            n_query = n_function if self.args.func < 0 or self.args.func > n_function else self.args.func
            self.log.info("Number of functions ...  " + str(n_function))
            self.log.info("Number of jobs ... " + str(n_query))
            all_results = ""
            try:
                for q in range(n_query):
                    query = queries[q]
                    function_name  = self.getFunctionName(query)
                    self.log.info("Checking feasibility of ...  " + str(function_name))
                    out = ""
                    try:
                        p = multiprocessing.Process(target=checkFeas, args=(self.args, q, smt2_file, ))
                        p.start()
                        p.join(self.args.timeout)
                        if p.is_alive():
                            out = out_message % (function_name, "TIMEOUT", "", "", "", "", "")
                            out = bcolors.WARNING + out + bcolors.ENDC
                            p.terminate()
                            p.join()
                    except Exception as e:
                        self.log.exception(str(e))
                        continue
                        all_results += out + "\n-----------------------\n"
                if self.args.save:
                    f_name = ntpath.basename(smt2_file)+"_feas.txt"
                    with open (f_name, "w") as f:
                        f.write(all_results)
            except Exception as e:
                self.log.exception(str(e))


    def parallelRun(self, smt2_file):
        """
        Job spanner
        """
        ctx = z3.Context ()
        fp = z3.Fixedpoint (ctx=ctx)
        jobs = []
        with stats.timer ('Parse'):
            self.log.info('Parsing  ... ' + str(smt2_file))
            queries = fp.parse_file (smt2_file)
            stats.stop('Parse')
            self.log.info("Parsing time ... " + str(stats.get('Parse')) + " ms")
            n_function = len(queries)
            n_query = n_function if self.args.func < 0 or self.args.func > n_function else self.args.func
            self.log.info("Number of functions ...  " + str(n_function))
            self.log.info("Number of jobs ... " + str(n_query))
            all_results = ""
            pool_jobs = Pool(processes=n_query)
            try:
                for q in range(n_query):
                    query = queries[q]
                    function_name  = self.getFunctionName(query)
                    self.log.info("Checking feasibility of ...  " + str(function_name))
                    #job_result = pool_jobs.apply_async(jobStarter, (self.args, qi, smt2_file, ), callback=self.onReturn)
                    job_result = pool_jobs.apply_async(jobStarter, (self.args, q, smt2_file, ))
                    job_result.wait(timeout=self.args.timeout)
                    if job_result.ready():
                        out = ""
                        try:
                            out = job_result.get()
                            if bench: print out
                        except Exception as e:
                            print str(e)
                            continue
                        all_results += out + "\n-----------------------\n"
                    else:
                        out = out_message % (function_name, "TIMEOUT", "", "", "", "", "")
                        out = bcolors.WARNING + out + bcolors.ENDC
                        if bench: print out
                        all_results += out + "\n------- ----------------\n"
                pool_jobs.close()
                pool_jobs.terminate()
                pool_jobs.join()
                if self.args.save:
                    f_name = ntpath.basename(smt2_file)+"_feas.txt"
                    with open (f_name, "w") as f:
                        f.write(all_results)
                else:
                    print "\n\t ========= SUMMARY SEAHORN INCONSISTENCY CHECKS   ========"
                    print all_results
            except Exception as e:
                self.log.exception(str(e))


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
    p.add_argument ('--smt2', dest='is_smt2',
                    help='Benchmark file is in smt2 format',
                    action='store_true', default=False)
    p.add_argument ('--seapp', dest='seapp',
                    help='Enable Seahorn preprocessor',
                    action='store_true', default=False)
    p.add_argument ('--ms', dest='ms',
                    help='Enable Mixed Semantics transformation',
                    action='store_true', default=False)
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
    p.add_argument ('--stat', help='Print statistics', dest="stat",
                    default=False, action='store_true')
    p.add_argument ('--verbose', help='Verbose', action='store_true',
                    default=False, dest="verbose")
    p.add_argument ('--spacer_verbose', help='Spacer Verbose', action='store_true',
                    default=False, dest="z3_verbose")
    p.add_argument ('--bench', help='Output Benchmarking Info', action='store_true',
                    default=False, dest="bench")
    p.add_argument ('--inv', help='Output Invariants', action='store_true',
                    default=False, dest="inv")
    p.add_argument ('--save', help='Save results file', action='store_true',
                    default=False, dest="save")
    p.add_argument ('--timeout', help='Timeout per function',
                    type=float, default=20.00, dest="timeout")
    p.add_argument ('--func', help='Number of functions',
                    type=int, default=-1, dest="func")
    p.add_argument ('-O', type=int, dest='opt_level', metavar='INT',
                     help='Optimization level L:[0,1,2,3]', default=0)
    p.add_argument ('--track',
                    help='Track registers, pointers, and memory',
                    choices=['reg', 'ptr', 'mem'], default='mem')
    p.add_argument ('--bc', dest='bc',
                    help='LLVM bitecode format',
                    action='store_true', default=False)
    p.add_argument ('--entry', metavar='FUNCNAME', dest='entry_point',
                    help='Entry point to the program (--seapp must be enabled)', default=None)
    p.add_argument ('--no_dl', help='Disable Difference Logic (UTVPI) in SPACER', action='store_true',
                    default=False, dest="utvpi")
    pars = p.parse_args (argv)
    global verbose
    verbose = pars.verbose
    global bench
    bench = pars.bench
    return pars


def stat (key, val): stats.put (key, val)

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

            if args.ms:
                ms_out = defMSName (in_name, workdir)
                mixSem (in_name, ms_out, args=args)
                in_name = ms_out

        if args.opt_level > 0:
            opt_out = defOPTName (in_name, args.opt_level, workdir)
            llvmOpt (in_name, opt_out, args.opt_level)
            in_name = opt_out


        smt_out = defSMTName(in_name, workdir)
        seahorn_args = []
        seahorn_args.extend (['-horn-sem-lvl={0}'.format (args.track)])

        seahorn (in_name, smt_out, seahorn_args)
        in_name = smt_out

    jb = JobsSpanner(args)
    jb.spanner(in_name)


# if __name__ == '__main__':
#     res = None
#     try:
#         main (sys.argv)
#     except Exception as e:
#         print str(e)
#     sys.exit (res)
