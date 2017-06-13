#!/usr/bin/env python

import sys
import os
import os.path
import atexit
import tempfile
import shutil
import subprocess as sub
import threading
import signal
import resource
import stats



root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose = True


running_process = None


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

def loadEnv (filename):
    if not os.path.isfile (filename): return

    f = open (filename)
    for line in f:
        sl = line.split('=', 1)
        # skip lines without equality
        if len(sl) != 2:
            continue
        (key, val) = sl

        os.environ [key] = os.path.expandvars (val.rstrip ())

        
def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='SeaHorn Verification Framework')
    p.add_argument ('-o', dest='out_name', metavar='FILE',
                       help='Output file name')
    p.add_argument ("--save-temps", dest="save_temps",
                       help="Do not delete temporary files",
                       action="store_true",
                       default=False)
    p.add_argument ("--temp-dir", dest="temp_dir", metavar='DIR',
                       help="Temporary directory",
                       default=None)
    p.add_argument ("--time-passes", dest="time_passes",
                       help="Time LLVM passes",
                       default=False, action='store_true')
    p.add_argument ('-O', type=int, dest='L', metavar='INT',
                       help='Optimization level L:[0,1,2,3]', default=3)
    p.add_argument ('-g', default=False, action='store_true', dest='debug_info',
                    help='Compile with debug information')
    p.add_argument ('-m', type=int, dest='machine',
                       help='Machine architecture MACHINE:[32,64]', default=32)
    p.add_argument ('--engine', '-e', type=str, dest='engine', metavar='STR',
                       help='Verification engine', default='spacer')
    p.add_argument ('--cpu', type=int, dest='cpu', metavar='SEC',
                       help='CPU time limit (seconds)', default=-1)
    p.add_argument ('--mem', type=int, dest='mem', metavar='MB',
                       help='MEM limit (MB)', default=-1)
    p.add_argument ('--cex', dest='cex', help='Destination for a cex',
                       default=None, metavar='FILE')
    p.add_argument ('--use-z3-smt2', dest='use_z3_smt2',
                       help='Use z3_smt2.py to run spacer',
                       default=False, action='store_true')
    p.add_argument ('--run-z3', dest='run_z3', help='Run Z3 after generating smt2 file',
                       default=False, action='store_true')
    p.add_argument ('--inline', dest='inline', help='Inline all functions',
                    default=False, action='store_true')
    p.add_argument ('file', metavar='FILE', help='Input file')

    args = p.parse_args (argv)
    
    if args.L < 0 or args.L > 3:
        p.error ("Unknown option: -O%s" % args.L)

    if args.machine != 32 and args.machine != 64:
        p.error ("Unknown option -m%s" % args.machine)

    if args.engine != 'pdr' and args.engine != 'spacer':
        p.error ("Unknown option --engine=%s" % args.engine)
        
    return args

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
        raise IOError ("Cannot find opt")
    return opt

def getSeahorn ():
    seahorn = None
    if 'SEAHORN' in os.environ: seahorn = os.environ ['SEAHORN']
    if not isexec (seahorn):
        seahorn = os.path.join (root, "bin/seahorn")
    if not isexec (seahorn): seahorn = which ('seahorn')
    if not isexec (seahorn):
        raise IOError ("Cannot find seahorn")
    return seahorn

def getSeaPP ():
    seapp = None
    if 'SEAPP' in os.environ:
        seapp = os.environ ['SEAPP']
    if not isexec (seapp):
        seapp = os.path.join (root, "bin/seapp")
    if not isexec (seapp): seapp = which ('seapp')
    if not isexec (seapp):
        raise IOError ("Cannot find seahorn pre-processor")
    return seapp

def getClang ():
    names = ['clang-mp-3.8', 'clang-3.8', 'clang']
    
    for n in names:
        clang = which (n)
        if clang is not None:
            return clang
    raise IOError ('Cannot find clang (required)')    

def getSpacer ():
    spacer = None
    if 'SPACER' in os.environ:
        spacer = os.environ ['SPACER']
    if not isexec (spacer):
        spacer = os.path.join (root, "bin/z3")
    if not isexec (spacer): spacer = which ('z3')
    if not isexec (spacer):
        raise IOError ("Cannot find spacer")
    return spacer

def getZ3Smt2():
    f = None
    if 'Z3_SMT2' in os.environ:
        f = os.environ ['Z3_SMT2']
    if not isexec (f):
        f = os.path.join (root, 'bin/z3_smt2.py')
    if not isexec (f): f = which ('z3_smt2.py')
    if not isexec (f):
        raise IOError ('Cannot find z3_smt2.py')
    return f

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
    fname = os.path.splitext (base)[0] + '.ms.bc'
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
    sub.check_call (clang_args)

# Run seapp
def seapp (in_name, out_name, arch, args, extra_args=[]):
    if out_name == '' or out_name == None:
        out_name = defPPName (in_name)

    seapp_args = [getSeaPP (), '-o', out_name, in_name ]
    if args.inline: seapp_args.append ('--horn-inline-all')
    seapp_args.extend (extra_args)

    if verbose: print ' '.join (seapp_args)
    sub.check_call (seapp_args)

def sharedLib (base):
    ext = '.so'
    if sys.platform.startswith ('darwin'): ext = '.dylib'
    return base + ext

# Run Mixed Semantics
def mixSem (in_name, out_name, arch=32, extra_args=[]):
    if out_name == '' or out_name == None:
        out_name = defMSName (in_name)

    opt = getOpt ()
    mixLib = sharedLib (os.path.join (root, 'lib/shadow'))
    
    ms_args = [opt, "-load", mixLib, '-lowerswitch',
               '-mixed-semantics', '-o', out_name, in_name]
    ms_args.extend (extra_args)

    if verbose: print ' '.join (ms_args)
    sub.check_call (ms_args)

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

    opt = sub.Popen (opt_args, stdin=open (in_name),
                     stdout=sub.PIPE, preexec_fn=set_limits)
    output = opt.communicate () [0]

    if opt.returncode != 0:
        raise sub.CalledProcessError (opt.returncode, opt_args)

# Run SeaHorn
def seahorn (in_name, out_name, opts, cex = None, cpu = -1, mem = -1):
    def set_limits ():
        if mem > 0:
            mem_bytes = mem * 1024 * 1024
            resource.setrlimit (resource.RLIMIT_AS, [mem_bytes, mem_bytes])

    seahorn_cmd = [ getSeahorn(), in_name,
                    '-horn-inter-proc',
                    '-horn-sem-lvl=mem',
                    '-horn-step=large',
                    '-o', out_name]
    seahorn_cmd.extend (opts)
    if cex is not None: seahorn_cmd.append ('--horn-svcomp-cex={}'.format (cex))
    if verbose: print ' '.join (seahorn_cmd)

    p = sub.Popen (seahorn_cmd, preexec_fn=set_limits)

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


def is_seahorn_opt (x):
    if x.startswith ('-'):
        y = x.strip ('-')
        return y.startswith ('horn') or y.startswith ('crab') or y.startswith ('log')
    return False

def is_z3_opt (x):
    return x.startswith ('--z3-')

def is_non_seahorn_opt (x): return not (is_seahorn_opt (x) or is_z3_opt (x))


def runSpacer (in_name, engine, cpu=-1, extra_args=[]):
    run_engine = 'fixedpoint.engine=' + engine
    spacer_args = [getSpacer (),
                   'fixedpoint.xform.slice=false',
                   'fixedpoint.xform.inline_linear=false',
                   'fixedpoint.xform.inline_eager=false',
                   'fixedpoint.use_heavy_mev=true',
	           'fixedpoint.pdr.flexible_trace=true',
	           'fixedpoint.reset_obligation_queue=true',
                   run_engine, in_name ]
    if verbose: print ' '.join (spacer_args)
    stat ('Result', 'UNKNOWN')
    result = None
    try:
        p = sub.Popen (spacer_args, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
        result,_ = p.communicate()
    except Exception as e:
        print str(e)
        
    if 'unsat' in result:
        stat('Result', 'SAFE')
    elif 'sat' in result:
        stat('Result', 'CEX')

def runZ3 (in_name, z3_args):
    z3fe = getZ3Smt2 ()
    args = [z3fe]
    # strip of '--z3-' prefix
    for arg in z3_args:
        args.append ('--' + arg[len('--z3-'):])
    args.append (in_name)
    if verbose: print ' '.join (args)
    try:
        p = sub.Popen (args, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
        result,_ = p.communicate ()
    except Exception as e:
        print str(e)
    print result


def stat (key, val): stats.put (key, val)
def main (argv):
    stat ('Progress', 'UNKNOWN')
    os.setpgrp ()
    loadEnv (os.path.join (root, "env.common"))

    ## add directory containing this file to the PATH
    os.environ ['PATH'] =  os.path.dirname (os.path.realpath (__file__)) + \
                           os.pathsep + os.environ['PATH']
    
    seahorn_args = filter (is_seahorn_opt, argv [1:])
    z3_args = filter (is_z3_opt, argv [1:])
    argv = filter (is_non_seahorn_opt, argv [1:])

    args  = parseArgs (argv)

    workdir = createWorkDir (args.temp_dir, args.save_temps)

    in_name = args.file

    bc_out = defBCName (in_name, workdir)
    assert bc_out != in_name
    with stats.timer ('Clang'):
        extra_args = []
        if args.debug_info:
            extra_args.append ('-g')
        clang (in_name, bc_out, arch=args.machine, extra_args=extra_args)
    stat ('Progress', 'CLANG')

    in_name = bc_out

    pp_out = defPPName (in_name, workdir)
    assert pp_out != in_name
    with stats.timer ('Seapp'):
        seapp (in_name, pp_out, arch=args.machine, args=args)
    stat ('Progress', 'SEAPP')

    in_name = pp_out

    ms_out = defMSName (in_name, workdir)
    assert ms_out != in_name
    with stats.timer ('Mixed'):
        mixSem (in_name, ms_out, arch=args.machine)
    stat ('Progress', 'MIXED')

    in_name = ms_out

    opt_out = defOPTName (in_name, args.L, workdir)
    with stats.timer ('Opt'):
        llvmOpt (in_name, opt_out,
                 opt_level=args.L, time_passes=args.time_passes)
    stat ('Progress', 'OPT')

    in_name = opt_out

    smt_out = defSMTName(in_name, workdir)
    with stats.timer ('Seahorn'):
        seahorn (in_name, smt_out, seahorn_args, cex=args.cex, cpu=args.cpu, mem=args.mem)
    stat ('Progress', 'SMT2')

    if args.out_name is not None and args.out_name != smt_out:
        if verbose: print 'cp {0} {1}'.format (smt_out, args.out_name)
        shutil.copy2 (smt_out, args.out_name)

    if (args.run_z3):
        if args.use_z3_smt2: runZ3 (smt_out, z3_args)
        else: runSpacer (smt_out, args.engine, cpu=args.cpu)

    return 0

def killall ():
    global running_process
    if running_process != None:
        running_process.terminate ()
        running_process.kill ()
        running_process.wait ()
        running_process = None

if __name__ == '__main__':
    # unbuffered output
    sys.stdout = os.fdopen (sys.stdout.fileno (), 'w', 0)
    try:
        signal.signal (signal.SIGTERM, lambda x, y: killall ())
        sys.exit (main (sys.argv))
    except KeyboardInterrupt: pass
    finally:
        killall ()
        stats.brunch_print ()
