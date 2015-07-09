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


root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose=False
bench=False

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

def which(program):
    fpath, fname = os.path.split(program)
    if fpath:
        if isexec (program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            exe_file = os.path.join(path, program)
            if isexec (exe_file):
                return exe_file
    return None

def kill (proc):
    try:
        proc.terminate ()
        proc.kill ()
        proc.wait ()
        global running_process
        running_process = None
    except OSError:
        pass

def createWorkDir (dname = None, save = False):
    if dname is None:
        workdir = tempfile.mkdtemp (prefix='seahorn-')
    else:
        workdir = dname

    if verbose:
        print "Working directory", workdir

    if not save:
        atexit.register (shutil.rmtree, path=workdir)
    return workdir


def getOpt ():
    opt = None
    if 'OPT' in os.environ:
        opt = os.environ ['OPT']
    if not isexec (opt):
        opt = os.path.join (root, 'bin/seaopt')
    if not isexec (opt):
        opt = os.path.join (root, "bin/opt")
    if not isexec (opt): opt = which ('opt')
    if not isexec (opt):
        raise IOError ("Cannot find opt. Set OPT variable")
    return opt

def getSeahorn ():
    seahorn = None
    if 'SEAHORN' in os.environ: seahorn = os.environ ['SEAHORN']
    if not isexec (seahorn):
        seahorn = os.path.join (root, "bin/seahorn")
    if not isexec (seahorn): seahorn = which ('seahorn')
    if not isexec (seahorn):
        raise IOError ("Cannot find seahorn. Set SEAHORN variable.")
    return seahorn

def getSeaPP ():
    seapp = None
    if 'SEAPP' in os.environ:
        seapp = os.environ ['SEAPP']
    if not isexec (seapp):
        seapp = os.path.join (root, "bin/seapp")
    if not isexec (seapp): seapp = which ('seapp')
    if not isexec (seapp):
        raise IOError ("Cannot find seahorn pre-processor. Set SEAPP variable")
    return seapp

def getClang ():
    names = ['clang-mp-3.6', 'clang-3.6', 'clang', 'clang-mp-3.5', 'clang-mp-3.4']

    for n in names:
        clang = which (n)
        if clang is not None:
            return clang
    raise IOError ('Cannot find clang (required)')

### Passes
def defBCName (name, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + '.bc'
    return os.path.join (wd, fname)
def defPPName (name, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + '.pp.bc'
    return os.path.join (wd, fname)
def defMSName (name, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + 'ms.pp.bc'
    return os.path.join (wd, fname)
def defLlName (name, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + '.ll'
    return os.path.join (wd, fname)
def defOPTName (name, optLevel=3, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + '.o{}.bc'.format (optLevel)
    return os.path.join (wd, fname)
def defSMTName (name, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + '.smt2'
    return os.path.join (wd, fname)

# Run Clang
def clang (in_name, out_name, arch=32, extra_args=[]):
    if out_name == '' or out_name == None:
        out_name = defBCName (in_name)

    clang_args = [getClang (), '-emit-llvm', '-o', out_name, '-c', in_name ]
    clang_args.extend (extra_args)

    if verbose: print ' '.join (clang_args)
    subprocess.check_call (clang_args)

# Run seapp
def seapp (in_name, out_name, arch, args, extra_args=[]):
    if out_name == '' or out_name == None:
        out_name = defPPName (in_name)

    seapp_args = [getSeaPP (), '-o', out_name, in_name ]
    seapp_args.extend (extra_args)

    if args.entry_point is not None:
      seapp_args.extend ([''.join (['--entry-point=\"',args.entry_point,'\"'])])

    if verbose: print ' '.join (seapp_args)
    subprocess.check_call (seapp_args)

# Run Mixed Semantics
def mixSem (in_name, out_name, args, extra_args=[]):
    # we do not use args but we could make option --ms-reduce-main
    if out_name == '' or out_name == None:
        out_name = defMSName (in_name)

    ms_args = [getSeaPP (), '--horn-mixed-sem', '--ms-reduce-main', '-o', out_name, in_name ]
    ms_args.extend (extra_args)

    if verbose: print ' '.join (ms_args)
    subprocess.check_call (ms_args)

# Run Opt
def llvmOpt (in_name, out_name, opt_level=3, time_passes=False, cpu=-1):
    if out_name == '' or out_name is None:
        out_name = defOPTName (in_name, opt_level)
    import resource as r
    def set_limits ():
        if cpu > 0: r.setrlimit (r.RLIMIT_CPU, [cpu, cpu])

    opt = getOpt ()
    opt_args = [opt, '-f', '-funit-at-a-time']
    if opt_level > 0 and opt_level <= 3:
        opt_args.append ('-O{}'.format (opt_level))
    opt_args.extend (['-o', out_name ])

    if time_passes: opt_args.append ('-time-passes')

    if verbose: print ' '.join (opt_args)

    opt = subprocess.Popen (opt_args, stdin=open (in_name),
                     stdout=subprocess.PIPE, preexec_fn=set_limits)
    output = opt.communicate () [0]

    if opt.returncode != 0:
        raise subprocess.CalledProcessError (opt.returncode, opt_args)

# Run SeaHorn
def seahorn (in_name, out_name, opts, cex = None, cpu = -1, mem = -1):
    def set_limits ():
        if mem > 0:
            mem_bytes = mem * 1024 * 1024
            resource.setrlimit (resource.RLIMIT_AS, [mem_bytes, mem_bytes])

        out_name = defBCName (in_name)

    seahorn_cmd = [ getSeahorn(), in_name,
                    '-horn-step=feasiblesmall',
                    '-o', out_name,
                    '-oll', defLlName (out_name) ]
    seahorn_cmd.extend (opts)
    #if cex is not None: seahorn_cmd.append ('--horn-svcomp-cex={}'.format (cex))
    if verbose: print ' '.join (seahorn_cmd)

    p = subprocess.Popen (seahorn_cmd, preexec_fn=set_limits)

    global running_process
    running_process = p

    timer = threading.Timer (cpu, kill, [p])
    if cpu > 0: timer.start ()

    try:
        (pid, returnvalue, ru_child) = os.wait4 (p.pid, 0)
        running_process = None
    finally:
        ## kill the timer if the process has terminated already
        if timer.isAlive (): timer.cancel ()

    ## if seahorn did not terminate properly, propagate this error code
    if returnvalue != 0: sys.exit (returnvalue)



out_message = ("""
FUNCTION NAME = %s
RESULT = %s
SET OF INVARIANTS = %s
FEASIBLE FLAGS  = %s
INFEASIBLE FLAGS = %s
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
        #super(Feasibility, self).__init__()
        self.function_name = None
        #self.name = "Function_"+str(query_index)
        self._return = None
        #if verbose: multiprocessing.log_to_stderr(logging.DEBUG)



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
            out = out_message % (function_name, "FEASIBLE", "", "Trivial", "")
            out = bcolors.OKGREEN + out + bcolors.ENDC
            return out



    def checkFeas(self, expr_query):
        done = False
        rounds = 0 # counter for feasibility check
        self.ee_idx = self.ee_vars(expr_query)
        if verbose: print "EE VARS INDEX:", self.ee_idx
        out = ""
        function_name = self.function_name
        while not done:
            with stats.timer ('Query'):
                print "Query Round " + str(rounds) + " ... "
                res = self.fp.query (expr_query) #if round == 0 else self.fp.query_from_lvl(12, expr_query)
                if res == z3.sat:
                    msg = "ENTRY -> EXIT is FEASIBLE" if rounds==0 else "STILL FEASIBLE: Continue checking ..."
                    self.log.info("( " + function_name + " ) " + msg)
                    self.feasible_flag |= set(self.ee_idx)
                    expr_query, path = self.cex(expr_query)
                    rounds += 1
                    if expr_query is None:
                        result = "[%s], Feasible" % function_name
                        stat('Result', result)
                        stat('Rounds', str(rounds))
                        feas = list(self.feasible_flag)
                        infeas = list(self.non_feasible_flag)
                        out += out_message % (function_name, "FEASIBLE", "", str(feas),  str(infeas))
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
                        out += out_message % (function_name, "FEASIBLE", inv_info, str(feas), str([]))
                        out = bcolors.OKGREEN + out + bcolors.ENDC
                    else:
                        msg = "EXIT is not FEASIBLE" if rounds==0 else "INFEASIBLE BLOCK FOUND"
                        if rounds == 0:
                            self.feasible_flag.add(self.ee_idx[0])
                            self.non_feasible_flag.add(self.ee_idx[1])
                        self.log.info(" ( " + function_name + " ) " + msg)
                        feas = list(self.feasible_flag)
                        infeas = list(self.non_feasible_flag)
                        out += out_message % (function_name, "INFEASIBLE", inv_info, str(feas), str(infeas))
                        out = bcolors.FAIL + out + bcolors.ENDC
                    done = True
                else:
                    out += out_message % (function_name, "UNKNOWN", "", "", "")
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
        self.log.info("Inspecting the CEX ... ")
        raw_cex = self.fp.get_ground_sat_answer()
        ground_sat = get_conjuncts(raw_cex)
        if verbose: print "RAW CEX:", ground_sat
        fpred = ground_sat[0] if len(ground_sat[0].children()) != 0 else ground_sat[1] # inspecting the first predicate
        var_flags = self.getListFlags(fpred)
        self.flags = len(var_flags) + 1 # TODO Jorge
        true_idxs, false_idxs = self.tfFlags(fpred, self.flags)
        t_flags = [t for t in true_idxs if t not in self.ee_idx] # filter  entry/exit flags
        f_flags = [t for t in false_idxs if t not in self.ee_idx] # filter entry/exit flags
        self.feasible_flag |= set(t_flags)
        self.non_feasible_flag = set(f_flags)
        if verbose: print "TRUE FLAGS:" + str(t_flags) ,  "\nFALSE FLAGS:" + str(f_flags)
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
        if verbose: print "New Conjunct:", and_predicate
        new_exist_vars = self.existVars(exist_vars, true_false_vars)
        new_query = z3.Exists(new_exist_vars,and_predicate)
        if verbose: print "NEW Query:\n", new_query
        return new_query

    def mkVars(self, idxs, qr):
        """
        given a list of indexes return var names
        """
        vars = list()
        for idx in idxs:
            new_v = z3.Bool("__r"+str(idx)+"_0", qr.ctx)
            vars.append(new_v)
            # if z3.is_true(v):
            #     new_v = z3.Bool("__r"+str(idx)+"_0", qr.ctx)
            #     vars.append(new_v)
            # else:
            #     vars.append(v)
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



def jobStarter(args, query_index, smt2_file):
    job = Feasibility(args, smt2_file)
    out = job.run(query_index)
    return out



class JobsSpanner(object):
    def __init__(self, args):
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



    def spanner(self, smt2_file):
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
            n_function = len(queries)
            n_query = n_function if self.args.func < 0 or self.args.func > n_function else self.args.func
            print "Number of functions ...  " + str(n_function)
            print "Number of jobs ... " + str(n_query)
            all_results = ""
            pool_jobs = Pool(processes=n_query)
            try:
                for q in range(n_query):
                    query = queries[q]
                    function_name  = self.getFunctionName(query)
                    print "checking feasibility of function =>  " + function_name
                    #job_result = pool_jobs.apply_async(jobStarter, (self.args, qi, smt2_file, ), callback=self.onReturn)
                    job_result = pool_jobs.apply_async(jobStarter, (self.args, q, smt2_file, ))
                    job_result.wait(timeout=self.args.timeout)
                    if job_result.ready():
                        out = job_result.get()
                        #print out
                        all_results += out + "\n-----------------------\n"
                    else:
                        out = out_message % (function_name, "TIMEOUT", "", "", "")
                        out = bcolors.WARNING + out + bcolors.ENDC
                        print out
                        all_results += out + "\n-----------------------\n"
                pool_jobs.close()
                pool_jobs.terminate()
                pool_jobs.join()
                print "\n\t ========= OVERALL FEASIBILITY RESULTS ========"
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
    p.add_argument ('--inv', help='Output Invariants', action='store_true',
                    default=False, dest="inv")
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


if __name__ == '__main__':
    res = None
    try:
        main (sys.argv)
    except Exception as e:
        print str(e)
    finally:
        if bench: stats.brunch_print ()
    sys.exit (res)
