#!/usr/bin/env python

import sys
import os
import os.path
import subprocess as sub
from itertools import ifilterfalse 
import csv
import re

verbose = False

## XXX: defined in _init__.py 
# When this file is used as a module we just need to 
# add `from sea import which' before calling which. 
# However, there is some problem with paths when this file 
# is used as a python script (via main)
def which(program):
    if isinstance (program, str):
        choices = [program]
    else:
        choices = program

    def isexec (fpath):
        if fpath == None: return False
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    for p in choices:
        fpath, fname = os.path.split(p)
        if fpath:
            if isexec (p): return p
        else:
            for path in os.environ["PATH"].split(os.pathsep):
                exe_file = os.path.join(path, p)
                if isexec (exe_file):
                    return exe_file
    return None

## XXX: defined in _init__.py 
# When this file is used as a module we just need to 
# add `from sea import createWorkDir' before calling which. 
# However, there is some problem with paths when this file 
# is used as a python script (via main)
def createWorkDir (dname=None, save=False, prefix='tmp-'):
    import atexit
    import tempfile
    import shutil
    if dname is None:
        workdir = tempfile.mkdtemp (prefix=prefix)
    else:
        if not os.path.isdir (dname): os.mkdir (dname)
        workdir = dname

    if not save:
        atexit.register (shutil.rmtree, path=workdir)
    return workdir

# remaps a file based on working dir and a new extension
def remap_file_name (in_file, ext, work_dir):
    out_file = in_file
    if work_dir is not None:
        out_file = os.path.basename (in_file)
        out_file = os.path.join (work_dir, out_file)
    out_file = os.path.splitext (out_file)[0]
    out_file = out_file + ext
    return out_file

def get_sea ():
    #from sea import which 
    cmd_name = which (['sea'])
    if cmd_name is None: report_fatal_error('cannot find sea')
    return cmd_name

def get_gnu_parallel():
    #from sea import which 
    cmd_name = which (['parallel'])
    if cmd_name is None: report_fatal_error('cannot find GNU/Parallel')
    return cmd_name

def add_abc_args(ap):
    from argparse import RawTextHelpFormatter
    ap.formatter_class=RawTextHelpFormatter
    if ap.description is None:
        ap.description = 'Array bounds check analysis\n\n' + \
               'Description: the analysis instruments each memory access with an assertion that is\n' + \
               'satisfied iff the memory access is in-bounds. The analysis splits the\n' + \
               'original program into N instrumented programs and runs each one in parallel, where N\n' + \
               'is the number of heap and stack allocation sites. Each of the N instrumented programs\n' + \
               'instruments only the memory accesses confined in the corresponding allocation site.'

    ap.add_argument ('-O', type=int, dest='opt_level', metavar='INT',
                     help='Optimization level L:[0,1,2,3]', default=0)
    ap.add_argument ('--verbose', '-v', dest='verbose', type=int, default=0,
                     help='Verbosity level', metavar='N')
    ap.add_argument ('--zverbose', dest='zverbose', type=int, default=0,
                     help='Verbosity level for Z3', metavar='N')
    ap.add_argument ('--oll', dest='asm_out_file', default=None,
                         help='LLVM assembly output file')
    ap.add_argument ('--bmc', '-bmc', dest='bmc', type=int, default=-1,
                     help='Bounded-model checking using horn solver with bound N', metavar='N')
    ap.add_argument ('--do-not-split-proof', dest='dont_split_proof',
                     help='Do not split the proof by allocation sites',
                     default=False, action='store_true')
    # XXX for debugging: this might produce quite different proofs from --do-not-split-proof
    ap.add_argument ('--sequential', dest='sequential',
                     help="if do-not-split-proof is disabled then prove \n"
                           "each allocation site separately but sequentially "
                           "(default parallel) ",
                     default=False, action='store_true')
    ap.add_argument ('--only-alloc-site', dest='alloc_site', type=int, default=-1,
                     help='Only instrument checks from this allocation site', metavar='N')
    ap.add_argument ('--add-extra-cutpoints', 
                     help="Add additional cutpoints:\n"
                          "- h0: none\n"
                          "- h1: add block if source of a back-edge\n"
                          "- h2: add block if it reaches more cutpoints than its successors\n",
                     choices=['h0','h1','h2'], dest='add_cuts', default='h0')
    ap.add_argument ('--externalize-functions',
                     help='Externalize these functions',
                     dest='extern_funcs', type=str, metavar='str,...')
    ap.add_argument ('--abstract-functions',
                     help="Abstract all calls to these functions.\n"
                          "Similar effect as --externalize-functions but at the level of horn clauses\n",
                     dest='abstract_funcs', type=str, metavar='str,...')
    ap.add_argument ('--abstract-memory',
                     help='Abstract memory instructions', dest='abs_mem_lvl',
                     choices = ['none','only-load','only-store','load-and-store'],
                     default='none')
    ap.add_argument ('--dsa', 
                     help="Dsa analysis:\n"
                          "- llvm    : context-insensitive Llvm Dsa\n"
                          "- sea-flat: flat memory SeaHorn Dsa\n"
                          "- sea-ci  : context-insensitive SeaHorn Dsa\n"
                          "- sea-cs  : context-sensitive SeaHorn Dsa\n",
                     choices=['llvm','sea-flat','sea-ci','sea-cs'], dest='dsa', default='llvm')
    ap.add_argument ('--abc-disable-underflow', dest='abc_no_under',
                     help='Do not instrument underflow checks',
                     default=False, action='store_true')
    ap.add_argument ('--abc-disable-reads', dest='abc_no_reads',
                     help='Do not instrument memory reads',
                     default=False, action='store_true')
    ap.add_argument ('--abc-disable-writes', dest='abc_no_writes',
                     help='Do not instrument memory writes',
                     default=False, action='store_true')
    ap.add_argument ('--abc-disable-mem-intrinsics', dest='abc_no_intrinsics',
                     help='Do not instrument memcpy, memmove, and memset',
                     default=False, action='store_true')
    ap.add_argument ('--abc-escape-ptr', dest='abc_escape_ptr',
                     help='Keep track whether a pointer escapes',
                     default=False, action='store_true')
    ap.add_argument ('--abc-use-deref', dest='abc_use_deref',
                     help='Use dereferenceable attribute to add extra assumptions',
                     default=False, action='store_true')
    ap.add_argument ('--abc-track-base-only', dest='abc_track_base_only',
                     help='Track only accesses to base pointers',
                     default=False, action='store_true')
    ap.add_argument ('--abc-surface-only', dest='abc_surface_only',
                     help='Track only accesses to pointers which are not stored in memory',
                     default=False, action='store_true')
    ap.add_argument ('--abc-store-base-only', dest='abc_store_base_only',
                     help='Check only base pointers are stored in memory',
                     default=False, action='store_true')
    ap.add_argument ('--csv', dest='csv_file',
                     help='Write results to a csv file',
                     metavar='DIR', default='out.csv')
    return ap
    
def report_fatal_error (msg, returncode = None):
    if returncode is not None:          # returncode is a 16-bit integer
        exitcode = returncode // 256    # 8 most significant bits returned value by exit()
        returnsignal = returncode % 256 # 8 least significant bits returned value by waitpid()
        if exitcode <> 0:
            print "EXIT CODE " + str(exitcode)
        if returnsignal == 9 or returnsignal == (128+9):
            print "KILLED BY SIGNAL 9"
        if returnsignal <> 0:
            print "KILLED BY SIGNAL " + str(returnsignal)
    sys.exit("ERROR found in abc.py: " + msg)


def get_answer(output):
    if "BRUNCH_STAT Result TRUE" in output:
        return True
    elif "BRUNCH_STAT Result FALSE" in output:
        return False
    else:
        return None

def get_num_checks (output):
    pattern = re.compile(r'-- (\d+).*Total number.*added checks$')
    for line in output.splitlines():
        match = pattern.search(str(line))
        if match:
            return int(match.group(1))
    return None

def get_time (output):
    pattern = re.compile(r'BRUNCH_STAT seahorn_total (\d+)\.(\d+).*')
    for line in output.splitlines():
        match = pattern.search(str(line))
        if match:
            return float (str(match.group(1)) + "." + str(match.group(2)))
    return None

def get_invars_size (output):
    pattern1 = re.compile(r'BRUNCH_STAT NumOfBlocksWithInvariants (\d+).*')
    pattern2 = re.compile(r'BRUNCH_STAT SizeOfInvariants (\d+).*')
    total_num_of_blocks = -1
    total_invars_size = -1
    for line in output.splitlines():
        match = pattern1.search(str(line))
        if match:
            total_num_of_blocks = int (str(match.group(1)))
        match = pattern2.search(str(line))
        if match:
            total_invars_size = int (str(match.group(1)))
    return (total_num_of_blocks, total_invars_size)

def get_results (output, returnvalue, timeout):
    num_checks = get_num_checks (output)
    total_time = get_time(output)
    num_blks, invars_size = get_invars_size(output)
    exitcode = returnvalue // 256
    signalcode = returnvalue % 256
    ans = None
    if returnvalue == 0:
        ans = get_answer (output)
    else:
        if timeout > -1 : total_time = float(timeout)
    return (num_checks, ans, total_time, num_blks, invars_size, exitcode, signalcode)

# options for `sea pp`
def pp_opts (args):
    opts = ['--kill-vaarg=true',
            '--inline-allocators',                        
            ## XXX: this one seems buggy somehow:
            ##      it leaves the call graph in an inconsistent state.
            #'--inline-constructors', 
            '--unfold-loops-for-dsa',
            '--simplify-pointer-loops', 
            '--lower-invoke', 
            '--devirt-functions', 
            '--externalize-addr-taken-funcs']
    if args.extern_funcs is not None:
        opts.extend(['--externalize-functions={0}'.format(args.extern_funcs)])
    if args.abs_mem_lvl <> 'none':
        opts.extend (['--abstract-memory={0}'.format(args.abs_mem_lvl)])
                      
    return opts
    
# extra options for `sea pp` with array bounds checks
def abc_opts(args, alloca_id = None):    
    opts = ['--abc=global', '--abc-dsa-stats']
    if args.abc_no_under: opts.extend(['--abc-disable-underflow'])
    if args.abc_no_reads: opts.extend(['--abc-disable-reads'])
    if args.abc_no_writes: opts.extend(['--abc-disable-writes'])
    if args.abc_no_intrinsics: opts.extend(['--abc-disable-mem-intrinsics'])
    if args.abc_escape_ptr: opts.extend(['--abc-escape-ptr'])
    if args.abc_use_deref: opts.extend(['--abc-use_deref'])
    if args.abc_track_base_only: opts.extend(['--abc-track-base-only'])
    if args.abc_surface_only: opts.extend(['--abc-surface-only'])
    if args.abc_store_base_only: opts.extend(['--abc-store-base-only'])
    if alloca_id is not None: opts.extend(['--abc-alloc-site={0}'.format(str(alloca_id))])
    return opts

# options for `sea ms`
def ms_opts(args):
    opts = ['--symbolize-constant-loop-bounds']
    return opts

# options for `sea opt`
def opt_opts(args):
    opts = [#'--enable-indvar'
            #,'--enable-loop-idiom'
            '--enable-nondet-init'
            #,'--llvm-inline-threshold=150'
            #,'--llvm-unroll-threshold=150'
            ]
    return opts

# options for `sea horn`
def horn_opts(args):
    opts =  ['--track=mem',
             '--step=large',
             '--keep-shadows=true',
             '--horn-answer',
             '--horn-singleton-aliases=true',
             '--horn-global-constraints=true',
             '--horn-stats',
             '--horn-skip-constraints=true',
             '--horn-make-undef-warning-error=false',
             '--horn-child-order=false',
             '--horn-reduce-constraints',
             '--horn-use-write',
             '--horn-estimate-size-invars']
    if args.add_cuts is not 'h0':
        opts = opts + ['--horn-extra-cps={0}'.format(args.add_cuts)]

    opts = opts + ['--dsa={0}'.format(args.dsa)]

    if args.dsa != 'llvm':
        opts = opts + ['--horn-sea-dsa-split=true']
    if args.dsa == 'sea-cs':
        opts = opts + ['--horn-sea-dsa-local-mod=true']
        
    if args.abstract_funcs is not None:
        opts.extend(['--horn-abstract={0}'.format(args.abstract_funcs)])
            
    return opts

def csv_results_keys ():
    fmt = ['AllocId','NumChecks','Answer','Time','InvarsSize','BlocksWithInvars']
    return fmt

# flds is a list of fields    
def csv_results_header (results_file, flds):
    with open (results_file, 'w') as sf:
        writer = csv.writer (sf)
        writer.writerow (flds)

# create a lock for csv_writer
import threading
csv_writer_lock = threading.Lock()

# fmt is the list of fields
# res_dic is a dictionary 
def csv_results_line (filename, fmt, res_dic):
    line = list()
    for fld in fmt:
        if fld in res_dic: line.append (str (res_dic [fld]))
        else: line.append (None)
    with csv_writer_lock: # thread-safe using a lock
        with open (filename, 'a') as sf:
            writer = csv.writer (sf)
            writer.writerow (line)

def prove_abc_cmmd (in_file, alloca_id, args, extra = []):
    pf_cmd = list ()

    pf_cmd.extend(pp_opts(args))
    pf_cmd.extend(abc_opts(args, alloca_id))
    pf_cmd.extend(ms_opts(args))
    pf_cmd.extend(opt_opts(args))
    pf_cmd.extend(['-O{0}'.format(args.opt_level)])
    pf_cmd.extend(horn_opts(args))
    pf_cmd.extend(['--cpu={0}'.format(args.cpu), '--mem={0}'.format(args.mem)])
    pf_cmd.extend(['--verbose={0}'.format(args.zverbose)])
    if args.out_file is not None: 
        pf_cmd.extend (['-o', args.out_file])
    if args.asm_out_file is not None:
        asm_filename, asm_file_ext = os.path.splitext(args.asm_out_file)
        asm_filename = asm_filename + '.alloc.' + str(alloca_id) + asm_file_ext
        pf_cmd.extend(['--oll={0}'.format(asm_filename)])
    if args.bmc >=0 :
        pf_cmd = [get_sea(),'bpf', '--bound={0}'.format(args.bmc)] + pf_cmd + extra + [in_file]
    else:
        pf_cmd = [get_sea(), 'pf'] + pf_cmd + extra + [in_file]        
    return pf_cmd

# if alloca_id is None then it will try to prove all checks, 
# otherwise only those checks originated from alloca_id
def prove_abc (in_file, alloca_id, args, extra = []):

    if alloca_id is None:
        print "--- Running abc checker "
    else:
        print "--- Running abc checker for allocation site id=" + str(alloca_id)

    pf_cmd = prove_abc_cmmd(in_file, alloca_id, args, extra)

    if verbose: print " ".join(pf_cmd)

    p = sub.Popen(pf_cmd, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
    results, _ = p.communicate()
    print results
    checks, ans, time, blks, invars_size, exitcode, signalcode = get_results (results, p.returncode, args.cpu)
    if time == float(args.cpu):
        if "WARNING: found call to verifier.error()" in results:
            print "    SKIPPED: assertion found but unreachable from main"
        else:
            print " ".join(pf_cmd)                
            print "    Timeout!"
    elif checks == 0 or blks == invars_size:
        print "    Trivially safe (no checks or proven by frontend) "
    elif "WARNING: found call to verifier.error()" in results:
        print "    SKIPPED: assertion found but unreachable from main"
    elif verbose or args.zverbose > 0:
        print " ".join(pf_cmd)        
        print results
        
    return (checks, ans, time, blks, invars_size, exitcode, signalcode)


def print_results (outfile, num_allocas, orig_num_checks, isParallel):
    print "========================================="
    print "      Array bounds check analysis        "
    print "========================================="
    #print "Number of allocation sites=" + str(num_allocas)
    with open(outfile, 'rb') as csvfile:
        reader = csv.DictReader(csvfile)
        safe_allocas = 0
        total_time = 0.0
        total_checks = 0
        unsafe_allocas = []
        unproven_allocas = [] 
        for row in reader:
            total_checks = total_checks + int(row["NumChecks"])
            print "Results for allocation site id=" + str(row["AllocId"])
            print "\tNumber of array bounds checks=" + str(row["NumChecks"])
            ans = row["Answer"]
            if int(row["NumChecks"]) == 0: ans = 'True'
            print "\tAnswer=" + str(ans)
            time = 0.0 # it should whatever the timeout is
            if row["Time"] <> 'None': time = float(row["Time"])
            print "\tSolving time in seconds=" + str(time)
            print "-----------------------------------------"
            if ans == 'True' : 
                safe_allocas = safe_allocas + 1
            elif ans == 'False': 
                unsafe_allocas.append(row["AllocId"])
            else: 
                unproven_allocas.append(row["AllocId"])
            total_time = total_time + time

        print "************** BRUNCH STATS ***************** "
        print "BRUNCH_STAT Original number of array bounds checks " + str(orig_num_checks)
        print "BRUNCH_STAT Accumulated number of array bounds checks " + str(total_checks)
        if isParallel:
            print "BRUNCH_STAT Time " + str(total_time) + " (Not actual time just added individual times)"
        else:
            print "BRUNCH_STAT Time " + str(total_time)
        if (safe_allocas == num_allocas):
            print "BRUNCH_STAT Result TRUE"
        elif len(unsafe_allocas) > 0:
            print "BRUNCH_STAT Result FALSE"
            for a in unsafe_allocas:
                print "\tunsafe allocation site=" + str(a)
        elif len(unproven_allocas) > 0:
            print "BRUNCH_STAT Result UNKNOWN"
            print "Number of allocation sites=" + str(num_allocas)
            print "Number of unknown allocation sites=" + str(len(unproven_allocas))
            for a in unproven_allocas:
                print "\tcould not prove allocation site=" + str(a)
        print "************** BRUNCH STATS END ***************** "

# return a list with all allocation sites 
def get_alloc_sites (in_file, work_dir, args):
    opts = list ()
    opts.extend(pp_opts(args))
    opts.extend(abc_opts(args))
    
    alloca_file = work_dir + '/alloc.csv'

    opts.extend(['--abc-dsa-to-file=' + alloca_file])
    opts.extend(['--abc-dsa-stats'])
    opts.extend(['--abc-dsa={0}'.format (args.dsa)])
    
    opts = [get_sea(), 'pp'] + opts
    ext = '.pp.bc'
    out_file = remap_file_name (in_file, ext, work_dir)
    opts = opts + [in_file, '-o', out_file]
    p = sub.Popen(opts, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
    if verbose: print " ".join(opts)
    result, _ = p.communicate()
    if p.returncode <> 0:
        report_fatal_error('\n\n%s\n' % (result), p.returncode)
    allocas = []
    total_num_checks = get_num_checks (result)

    ## XXX: the relationship between allocation sites and nodes is
    ## many-to-many
    try:
        with open(alloca_file, 'rb') as csvfile:
            reader = csv.DictReader(csvfile)
            try:
                for row in reader:
                    ## XXX: these are comming from dsa nodes without
                    ## allocation site. The reason should be because the allocation 
                    ## site is located in an external function.
                    if row["alloc_site"] == '': continue

                    if int(row["alloc_site"]) not in allocas: 
                        allocas.append(int(row["alloc_site"]))
                allocas.sort()
            except csv.Error as e:
                report_fatal_error('file %s, line %d: %s' % (alloca_file, reader.line_num, e))
    except (IOError):
        report_fatal_error('file %s not found\n\n.%s\n' % (alloca_file, result))
    return (allocas, total_num_checks)

#############################################################################
#                Entry point called from commands.py                        #
#############################################################################
def sea_abc(args, extra): # extra is unused
    
    if args.verbose > 0: 
        global verbose
        verbose = True

    if os.path.isfile(args.csv_file):
        os.remove(args.csv_file)

    # from sea import createWorkDir
    work_dir = createWorkDir(args.temp_dir, args.save_temps, 'sea-abc-') 
    assert (len(args.in_files) == 1)
    in_file = args.in_files[0]

    if args.dont_split_proof or args.alloc_site >= 0:
        alloc_site = None
        if args.alloc_site >= 0: alloc_site = args.alloc_site
        num_checks,ans,time,num_blks,invars_size,_,_ = prove_abc(in_file, alloc_site, args)
        print "************** BRUNCH STATS ***************** "
        print "BRUNCH_STAT Number of array bounds checks " + str(num_checks)
        print "BRUNCH_STAT Time " + str(time)
        if ans == True: 
            print "BRUNCH_STAT Result TRUE"
        elif ans == False:
            print "BRUNCH_STAT Result FALSE"
        else:
            print "BRUNCH_STAT Result UNKNOWN"
        print "************** BRUNCH STATS END ***************** "
        ## XXX: do not write to a csv file because there is just one entry anyway.
        # fmt = csv_results_keys()
        # csv_results_header(args.csv_file, fmt)
        # results = dict ()
        # results['AllocId'] = -1; results['NumChecks'] = num_checks
        # results['Answer'] = ans; results['Time'] = time; 
        # results['InvarsSize'] = invars_size; results['BlocksWithInvars'] = num_blks
        # csv_results_line (args.csv_file, fmt, results)    
        return
    else:
        (allocas, num_checks) = get_alloc_sites (in_file, work_dir, args)
        num_allocas = len(allocas)
        #if verbose: print "Allocation sites = " + str(allocas)
        print "--- Found " + str(num_allocas) + " allocation sites"

        if num_allocas == 0:
            print "--- No allocation sites found so do nothing"
            return
        fmt = csv_results_keys()
        csv_results_header(args.csv_file, fmt)
        if args.sequential:  # for debugging purposes
            for alloca_id in allocas:
                num_checks,ans,time,num_blks,invars_size,_,_ = prove_abc(in_file, alloca_id, args)
                results = dict ()
                results['AllocId'] = alloca_id; results['NumChecks'] = num_checks
                results['Answer'] = ans; results['Time'] = time; 
                results['InvarsSize'] = invars_size; results['BlocksWithInvars'] = num_blks
                csv_results_line (args.csv_file, fmt, results)    
        else:
            xargs = []
            njobs = 0; acc_njobs = 0; maxjobs= 150 # this is tuneable!
            ## XXX: In principle, we could pass one single xargs to Popen first argument. 
            ## However, the maximum number of characters in Popen args is 131072.
            ## As a workaround split xargs into multiple ones.            
            for alloca_id in allocas:
                njobs = njobs + 1
                acc_njobs = acc_njobs + 1
                sea_abc_cmd = ['sea_abc', '--alloc-site={0}'.format(alloca_id), in_file, 
                               '--cpu={0}'.format(args.cpu), '--mem={0}'.format(args.mem),
                               '-O{0}'.format(args.opt_level), 
                               '--verbose={0}'.format(args.verbose), 
                               '--zverbose={0}'.format(args.zverbose), 
                               '--add-extra-cutpoints={0}'.format(args.add_cuts),
                               '--csv={0}'.format(args.csv_file)]
                if args.bmc >= 0 :
                    sea_abc_cmd.extend(['--bmc={0}'.format(args.bmc)])
                if args.extern_funcs is not None:
                    sea_abc_cmd.extend(['--externalize-functions={0}'.format(args.extern_funcs)])
                if args.abstract_funcs is not None:
                    sea_abc_cmd.extend(['--abstract-functions={0}'.format(args.abstract_funcs)])
                if args.abs_mem_lvl <> 'none':
                    sea_abc_cmd.extend (['--abstract-memory={0}'.format(args.abs_mem_lvl)])
                                         
                if args.abc_no_under: sea_abc_cmd.extend(['--abc-disable-underflow'])
                if args.abc_no_reads: sea_abc_cmd.extend(['--abc-disable-reads'])
                if args.abc_no_writes: sea_abc_cmd.extend(['--abc-disable-writes'])
                if args.abc_no_intrinsics: sea_abc_cmd.extend(['--abc-disable-mem-intrinsics'])
                if args.abc_escape_ptr : sea_abc_cmd.extend(['--abc-escape-ptr'])
                if args.abc_use_deref : sea_abc_cmd.extend(['--abc-use-deref'])
                if args.abc_track_base_only : sea_abc_cmd.extend(['--abc-track-base-only'])
                if args.abc_surface_only:    sea_abc_cmd.extend(['--abc-surface-only'])
                if args.abc_store_base_only: sea_abc_cmd.extend(['--abc-store-base-only'])

                sea_abc_cmd.extend(['--dsa={0}'.format(args.dsa)])

                if args.save_temps: 
                    sea_abc_cmd.extend(['--save-temps'])
                    sea_abc_cmd.extend(['--temp-dir={0}'.format(args.temp_dir)])

                xargs.append(' '.join(sea_abc_cmd))
                if njobs == maxjobs or acc_njobs == num_allocas:
                    if verbose: 
                        print "--- Running GNU parallel with "  + str(njobs) + " jobs."
                        for a in xargs:
                            print "\t" + str(a)

                    gnupar_opts = ['--no-notice']
                    #if verbose: gnupar_opts = gnupar_opts + ["--progress", "--eta"]
                    xargs = [get_gnu_parallel()] + gnupar_opts + [":::"] + xargs
                    #p = sub.Popen(xargs, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
                    p = sub.Popen(xargs, shell=False)
                    result, _ = p.communicate()
                    if p.returncode <> 0:  ## gnu parallel should not fail
                        report_fatal_error('\n\n%s\n' % (result), p.returncode)
                    if verbose or args.zverbose > 1: print str(result)
                    njobs = 0; xargs = []

                #assert (xargs == [])
        print_results (args.csv_file, len(allocas), num_checks, not args.sequential)


############################################################################
##                  Do not call this file as a script.                    ##
##          This is intended to be called only by GNU parallel            ## 
############################################################################

def _is_seahorn_opt (x):
    if x.startswith ('-'):
        y = x.strip ('-')
        return y.startswith ('horn') or \
            y.startswith ('crab') or y.startswith ('log')
    return False

def main (argv):
    import argparse
    from argparse import RawTextHelpFormatter
    ap = argparse.ArgumentParser (prog='sea_abc', 
                                  description='Script to run abc for a single allocation site',
                                  epilog='WARNING: should be used only by GNU parallel.\nUse instead \'sea abc\'',
                                  formatter_class=RawTextHelpFormatter)

    # from sea import add_in_out_args, add_tmp_dir_args
    # add_in_out_args(ap)
    ap.add_argument ('-o', dest='out_file',
                     metavar='FILE', help='Output file name', default=None)
    ap.add_argument ('in_files',  metavar='FILE', help='Input file', nargs='+')
    # add_tmp_dir_args(ap)
    ap.add_argument ('--save-temps', '--keep-temps',
                     dest="save_temps",
                     help="Do not delete temporary files",
                     action="store_true", default=False)
    ap.add_argument ('--temp-dir', dest='temp_dir', metavar='DIR',
                     help="Temporary directory", default=None)

    ap.add_argument ('--alloc-site', metavar='N', dest='alloca_id', 
                     help='Allocation site id',  type=int, required=True)    
    ap.add_argument ('--cpu', type=int, dest='cpu', metavar='SEC',
                       help='CPU time limit (seconds)', default=-1)
    ap.add_argument ('--mem', type=int, dest='mem', metavar='MB',
                       help='MEM limit (MB)', default=-1)
    add_abc_args(ap)

    all_opts = argv[1:]
    sea_opts = list(filter (_is_seahorn_opt, all_opts))
    rest_opts = list(ifilterfalse (_is_seahorn_opt, all_opts))

    #args = ap.parse_args (argv[1:])
    args = ap.parse_args (rest_opts)

    assert (len(args.in_files) == 1)

    if args.verbose > 0: 
        global verbose
        verbose = True

    #print "Started analysis for allocation site " +  str(args.alloca_id) + " ..."
    num_checks,ans,time,num_blks,invars_size,_,_ = prove_abc(args.in_files[0], args.alloca_id, args, sea_opts)
    fmt = csv_results_keys()
    results = dict ()
    results['AllocId'] = args.alloca_id; results['NumChecks'] = num_checks
    results['Answer'] = ans; results['Time'] = time
    results['InvarsSize'] = invars_size; results['BlocksWithInvars'] = num_blks
    csv_results_line (args.csv_file, fmt, results)    
    #print "num_checks" + str(num_checks)            
    #print "ans" + str(ans)            
    #print "time" + str(time)            

if __name__ == '__main__':
    res = None
    try:
        res = main (sys.argv)
    except Exception as e:
        print str(e)
    finally:
        sys.exit (res)
