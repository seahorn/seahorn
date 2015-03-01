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

def parseOpt (argv):
    from optparse import OptionParser

    parser = OptionParser ()
    parser.add_option ('-e', type='int', dest='engine',
                       help='Verification engine 0=PDR, 1=SPACER', default=1)
    parser.add_option ('--cpu', type='int', dest='cpu',
                       help='CPU time limit (seconds)', default=-1)
    parser.add_option ('--mem', type='int', dest='mem',
                       help='MEM limit (MB)', default=-1)
    parser.add_option ('--use-z3-script', dest='use_z3_script',
                       help='Use the python script in spacer repo to run z3',
                       default=False, action='store_true')
    parser.add_option ('--z3root', dest='z3root',
                       help='Root directory of z3',
                       default=None)


    (options, args) = parser.parse_args (argv)

    return (options, args)


def getSpacer ():
    spacer = None
    if 'SPACER' in os.environ:
        spacer = os.environ ['SPACER']
    if not isexec (spacer):
        spacer = os.path.join (root, "bin/z3")
    if not isexec (spacer):
        raise IOError ("Cannot find spacer")
    return spacer

def getZ3Frontend (z3root, build_dir):
    z3fe = None
    if z3root is None:
        z3root = os.path.join (root, build_dir + '/z3-prefix/src/z3')
    z3fe = os.path.join (z3root, 'stats/scripts/z3_smt2.py')
    return z3fe


def is_z3_opt (x):
    return x.startswith ('--z3-')


# Run Spacer (temporary fix, we need to push this function in )
def runSpacer (in_name, engine, cpu=-1, extra_args=[]):
    run_engine = "fixedpoint.engine=spacer" if engine==1 else "fixedpoint.engine=pdr"
    spacer_args = [getSpacer (),
                    "fixedpoint.slice=false",
                   "fixedpoint.use_heavy_mev=true",
	           "fixedpoint.flexible_trace=true",
	           "fixedpoint.reset_obligation_queue=true",
		   "fixedpoint.init_reach_facts=true",
                   "fixedpoint.print_statistics=true",
                   "-v:1",
                   run_engine, in_name ]
    if verbose: print ' '.join (spacer_args)
    stat ('Result', 'UNKNOWN')
    result = None
    try:
        p = sub.Popen (spacer_args, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
        result,_ = p.communicate()
    except Exception as e:
        print str(e)
    if "unsat" in result:
        stat("Result", "SAFE")
    elif "sat" in result:
        stat("Result", "CEX")


def runZ3 (in_name, z3root, build_dir, z3_args):
    z3fe = getZ3Frontend (z3root, build_dir)
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
    os.setpgrp ()
    loadEnv (os.path.join (root, "env.common"))

    z3_args = filter (is_z3_opt, argv [1:])

    (opt, args) = parseOpt (argv)

    smt_file = args [1]

    if opt.use_z3_script:
        runZ3(smt_file, opt.z3root, opt.build_dir, z3_args)
    else:
        runSpacer(smt_file, opt.engine, cpu=opt.cpu)

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
