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


root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose = False


def initProfiles():
    base = ['--step=large', '--track=reg', '--horn-stats', '--enable-nondet-init', '--externalize-addr-taken-funcs']
    profiles = dict()
    profiles ['inline'] = base + [ '-inline']
    profiles ['no_inline'] = base
    return profiles

profiles = initProfiles ()

def listProfiles ():
    for (k, v) in profiles.iteritems ():
        print k, ':', ' '.join (v)

def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

def parseOpt (argv):
    from optparse import OptionParser

    parser = OptionParser ()
    parser.add_option ("--save-temps", dest="save_temps",
                       help="Do not delete temporary files",
                       action="store_true",
                       default=False)
    parser.add_option ("--temp-dir", dest="temp_dir",
                       help="Temporary directory",
                       default=None)
    parser.add_option ('--cpu', type='int', dest='cpu',
                       help='CPU time limit (seconds)', default=-1)
    parser.add_option ('--mem', type='int', dest='mem',
                       help='MEM limit (MB)', default=-1)

    parser.add_option ('-m', type=int, dest='arch', default=32,
                       help='Machine architecture 32 or 64')
    parser.add_option ('--profiles', '-p', dest='profiles',
                       default='inline:no_inline',
                       help='Colon separated list of profiles')
    parser.add_option ('--list-profiles', dest='list_profiles',
                       action='store_true', default=False)
    parser.add_option ('--cex', dest='cex', default=None,
                       help='Destination for a counterexample file')
    parser.add_option ('--spec', default=None, help='Property file')

    (options, args) = parser.parse_args (argv)

    ## workarround the property file requirement
    if options.spec is not None:
        f = open (options.spec, 'r')
        l = f.readline ()
        # expect property of the form:
        # CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )
        if l.find ('__VERIFIER_error') < 0:
            print 'BRUNCH_STAT Result UNKNOWN'
            sys.exit (3)

    if options.list_profiles:
        listProfiles ()
        sys.exit (0)

    if options.arch != 32 and options.arch != 64:
        parser.error ('Unknown architecture {}'.format (opt.arch))

    if options.cex != None and os.path.isfile (options.cex):
        os.remove (options.cex)

    return (options, args)

def createWorkDir (dname = None, save = False):
    if dname == None:
        workdir = tempfile.mkdtemp (prefix='seahornpar-')
    else:
        workdir = dname

    if verbose: print "Working directory", workdir

    if not save: atexit.register (shutil.rmtree, path=workdir)
    return workdir

def getSea ():
    seahorn = os.path.join (root, "bin/sea")
    if not isexec (seahorn):
        raise IOError ("Cannot find sea")
    return seahorn

def cat (in_file, out_file): out_file.write (in_file.read ())

running = list()

def runSeahorn (args, fname, stdout, stderr):

    args = args + [fname]
    if verbose: print ' '.join (args)
    return sub.Popen (args,
                      stdout=open (stdout, 'w'),
                      stderr=open (stderr, 'w'))



def run (workdir, fname, sea_args = [], profs = [],
         cex = None, arch=32, cpu=-1, mem=-1):

    print "BRUNCH_STAT Result UNKNOWN"
    sys.stdout.flush ()

    sea_cmd = getSea()

    base_args = [sea_cmd, 'pf', '--mem={}'.format(mem),
                 '-m{}'.format (arch)]
    base_args.extend (sea_args)

    if cex != None:
        cex_base = os.path.basename (fname)
        cex_base = os.path.splitext (cex_base)[0]
        cex_base = os.path.join (workdir, cex_base)


    conf_name = list ()
    sea = list ()

    for prof in profs:
        conf_name.append (prof)
        p_args = base_args + profiles [prof]
        if cex != None:
            cex_name = '{}.{}.trace'.format (cex_base, prof)
            p_args.append ('--cex={}'.format (cex_name))
        sea.append (p_args)

    name = os.path.splitext (os.path.basename (fname))[0]
    stdout = [os.path.join (workdir, name + '_seahorn{}.stdout'.format (i))
              for i in range(len (sea))]
    stderr = [os.path.join (workdir, name + '_seahorn{}.stderr'.format (i))
              for i in range (len (sea))]
    global running
    running.extend ([runSeahorn (sea [i], fname, stdout[i], stderr [i])
                     for i in range (len (sea))])


    orig_pids = [p.pid for p in running]
    pids = [p.pid for p in running ]
    pid = -1
    returnvalue = -1
    while len (pids) != 0:
        print 'Running: ', pids

        (pid, returnvalue, ru_child) = os.wait4 (-1, 0)

        print 'Finished pid {0} with'.format (pid),
        print ' code {0} and signal {1}'.format((returnvalue // 256),
                                                (returnvalue % 256))
        pids.remove (pid)

        if returnvalue == 0:
            for p in pids:
                try:
                    os.kill (p, signal.SIGTERM)
                except OSError: pass
                finally:
                    try:
                        os.waitpid (p, 0)
                    except OSError: pass
            break

    if returnvalue == 0:
        idx = orig_pids.index (pid)
        cat (open (stdout [idx]), sys.stdout)
        cat (open (stderr [idx]), sys.stderr)
        if cex != None:
            cex_name = '{}.{}.trace'.format (cex_base, conf_name [idx])
            print 'Copying {} to {}'.format (cex_name, cex)
	    if os.path.isfile (cex_name):
                shutil.copy2 (cex_name, cex)
                print 'Counterexample trace is in {}'.format (cex)


        print 'WINNER: ', ' '.join (sea [idx])
        print 'BRUNCH_STAT config {0}'.format (idx)
        print 'BRUNCH_STAT config_name {0}'.format (conf_name [idx])

    else:
        print "ALL INSTANCES FAILED"
        print 'Calling sys.exit with {}'.format (returnvalue // 256)
        sys.exit (returnvalue // 256)

    running[:] = []
    return returnvalue

def seahorn_opt (x):
    if x.startswith ('-'):
        y = x.strip ('-')
        return y.startswith ('horn') or  y.startswith ('ikos')
    return False

def non_seahorn_opt (x): return not seahorn_opt (x)


def main (argv):

    seahorn_args = filter (seahorn_opt, argv [1:])
    argv = filter (non_seahorn_opt, argv [1:])

    (opt, args) = parseOpt (argv)

    workdir = createWorkDir (opt.temp_dir, opt.save_temps)
    returnvalue = 0
    for fname in args:
        returnvalue = run (workdir, fname, seahorn_args, opt.profiles.split (':'),
                           opt.cex, opt.arch, opt.cpu, opt.mem)
    return returnvalue

def killall ():
    global running
    for p in running:
        try:
            if p.poll () == None:
                p.terminate ()
                p.kill ()
                p.wait ()
                # no need to kill pg since it kills its children
        except OSError:   pass
    running[:] = []

if __name__ == '__main__':
    # unbuffered output
    sys.stdout = os.fdopen (sys.stdout.fileno (), 'w', 0)
    try:
        signal.signal (signal.SIGTERM, lambda x, y: killall())
        sys.exit (main (sys.argv))
    except KeyboardInterrupt: pass
    finally: killall ()
