#!/usr/bin/env python

# Minimalist (i.e., without optimizations) frontend for C programs
# compiled via GCC

# Requirements:
# - The version of dragonegg must match with llvm version used by
#   seahorn (e.g., dragonegg-3.4 and llvm-3.4)
# - getGcc () must be the same version that the one used during the
#   generation of the dragonegg library.

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

root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose = False

running_process = None

# Seahorn stuff

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
    parser.add_option ('-o', dest='out_name',
                       help='Output file name')
    parser.add_option ("--save-temps", dest="save_temps",
                       help="Do not delete temporary files",
                       action="store_true",
                       default=False)
    parser.add_option ("--temp-dir", dest="temp_dir",
                       help="Temporary directory",
                       default=None)
    parser.add_option ("--time-passes", dest="time_passes",
                       help="Time LLVM passes",
                       default=False, action='store_true')
    parser.add_option ('--no-seahorn', action='store_false',
                       dest='do_seahorn',
                       help='Only pre-process the files',
                       default=True)
    parser.add_option ('-m', type='int', dest='machine',
                       help='Machine architecture MACHINE:[32,64]', default=32)
    parser.add_option ('--cpu', type='int', dest='cpu',
                       help='CPU time limit (seconds)', default=-1)
    parser.add_option ('--mem', type='int', dest='mem',
                       help='MEM limit (MB)', default=-1)

    (options, args) = parser.parse_args (argv)

    if options.machine != 32 and options.machine != 64:
        parser.error ("Unknown option -m%s" % options.machine)

    return (options, args)

def createWorkDir (dname = None, save = False):
    if dname == None:
        workdir = tempfile.mkdtemp (prefix='seahorn-')
    else:
        workdir = dname

    if verbose:
        print "Working directory", workdir

    if not save:
        atexit.register (shutil.rmtree, path=workdir)
    return workdir

def sharedLib (base):
    ext = '.so'
    if sys.platform.startswith ('darwin'): ext = '.dylib'
    return base + ext

def getGcc ():
    gcc = which ("gcc")
    if gcc == None:
        raise IOError ("Cannot find gcc")
    return gcc

def getLlvmAs34 ():
    v = which ('llvm-as-3.4')
    if v is None: raise IOError ('Cannot find llvm-as-3.4')
    return v

def getDragonEggLib ():
    DragonEggLib = None
    if 'DRAGONEGG_LIB' in os.environ: 
        DragonEggLib = sharedLib("dragonegg")
        LlvmAirLib = os.path.join (os.environ ["DRAGONEGG_LIB"], DragonEggLib)
    elif 'DRAGONEGG' in os.environ: 
        DragonEggLib = sharedLib("dragonegg")
        LlvmAirLib = os.path.join (os.environ ["DRAGONEGG"], DragonEggLib)
    else:
        raise IOError ("Cannot find dragonegg library")
    return DragonEggLib

def getSeahorn ():
    seahorn = None
    if 'SEAHORN' in os.environ: 
        seahorn = os.environ ['SEAHORN']
    if not isexec (seahorn):
        seahorn = os.path.join (root, "bin/seahorn")
    if not isexec (seahorn):
        seahorn = which ("seahorn")
    if not isexec (seahorn):
        raise IOError ("Cannot find seahorn")
    return seahorn

def defBcName (name, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + '.llvm34.bc'
    return os.path.join (wd, fname)
def defLlName (name, wd=None):
    base = os.path.basename (name)
    if wd == None: wd = os.path.dirname  (name)
    fname = os.path.splitext (base)[0] + '.llvm34.ll'
    return os.path.join (wd, fname)

def LlvmAs (in_name, out_name):
    if out_name == '' or out_name == None: out_name = defBcName (in_name)
    LlvmAs_args = [getLlvmAs34 (), in_name, '-o', out_name ]
    if verbose: print ' '.join (LlvmAs_args)
    sub.check_call (LlvmAs_args)

def Gcc (in_name, out_name, arch=32):
    if out_name == '' or out_name == None: out_name = defBcName (in_name)

    out_name1 = defLlName (in_name)
    gcc_args = [getGcc (),
                '-m{}'.format (arch), '-c', in_name,
                "-fplugin=" + getDragonEggLib (), '-fplugin-arg-dragonegg-emit-ir', '-S',
                '-o', out_name1]
    if verbose: print ' '.join (gcc_args)
    sub.check_call (gcc_args)
    LlvmAs (out_name1, out_name)


def seahorn (in_name, opts, cpu = -1, mem = -1):
    def set_limits ():
        if mem > 0:
            mem_bytes = mem * 1024 * 1024
            resource.setrlimit (resource.RLIMIT_AS, [mem_bytes, mem_bytes])

    seahorn_cmd = [ getSeahorn() ]
    seahorn_cmd.extend (opts)
    seahorn_cmd.append (in_name)
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
        return y.startswith ('horn') or y.startswith ('crab') or y.startswith ('log') or y.startswith ('insert-checks')
    return False

def is_non_seahorn_opt (x): return not is_seahorn_opt (x)

def main (argv):
    os.setpgrp ()
    loadEnv (os.path.join (root, "env.common"))

    seahorn_args = filter (is_seahorn_opt, argv [1:])
    argv = filter (is_non_seahorn_opt, argv [1:])

    (opt, args) = parseOpt (argv)

    workdir = createWorkDir (opt.temp_dir, opt.save_temps)

    assert len(args) == 1
    in_name = args [0]

    do_bc = True
    do_seahorn = opt.do_seahorn

    (in_base, in_ext) = os.path.splitext (in_name)
    if in_ext == '.bc' :
        do_bc = False

    if do_bc:
        bc = defBcName (in_name, workdir)
        Gcc (in_name, bc, arch=opt.machine)
        in_name = bc

    if do_seahorn:
        seahorn (in_name, seahorn_args, cpu=opt.cpu, mem=opt.mem)
        in_name = None

    if opt.out_name != None and in_name != None and in_name != args [0]:
        shutil.copy2 (in_name, opt.out_name)

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
    finally: killall ()
