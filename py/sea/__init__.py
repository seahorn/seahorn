import os.path
import argparse

import os

import threading
import subprocess

import atexit
import tempfile
import shutil

def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

def which(program):
    if isinstance (program, str):
        choices = [program]
    else:
        choices = program

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
    
# inspired from:
# http://stackoverflow.com/questions/4158502/python-kill-or-terminate-subprocess-when-timeout
class TimeLimitedExec(threading.Thread):
    def __init__(self, cmd, cpu=0, mem=0, verbose=0):
        threading.Thread.__init__(self)
        self.cmd = cmd 
        self.cpu = cpu
        self.mem = mem
        self.p = None
        self.stdout = None
        self.stderr = None
        self.verbose = verbose

    def run(self, **popen_args):
        def set_limits ():
            import resource as r    
            if self.cpu > 0:
                r.setrlimit (r.RLIMIT_CPU, [self.cpu, self.cpu])
            if self.mem > 0:
                mem_bytes = self.mem * 1024 * 1024
                r.setrlimit (r.RLIMIT_AS, [mem_bytes, mem_bytes])
                
        if self.verbose > 0: print self.cmd
        self.p = subprocess.Popen(self.cmd, 
                                  preexec_fn=set_limits,
                                  **popen_args)
        self.stdout, self.stderr = self.p.communicate()

    def Run(self):
        self.start()

        if self.cpu > 0:
            self.join(self.cpu+5)
        else:
            self.join()

        if self.p is None:
            return -1
        
        if self.is_alive():
            print 'still alive, terminating'
            self.p.terminate()      
            self.join(5)

        if self.is_alive():
            print 'still alive after attempt to terminate, sending kill'
            self.p.kill()

        return self.p.returncode

    
def createWorkDir (dname=None, save=False, prefix='tmp-'):
    if dname is None:
        workdir = tempfile.mkdtemp (prefix=prefix)
    else:
        if not os.path.isdir (dname): os.mkdir (dname)
        workdir = dname

    if not save:
        atexit.register (shutil.rmtree, path=workdir)
    return workdir

def add_in_out_args (ap):
    ap.add_argument ('-o', dest='out_file',
                     metavar='FILE', help='Output file name', default=None)
    ap.add_argument ('in_file',  metavar='FILE', help='Input file')
    return ap

class CliCmd (object):
    def __init__ (self, name='', help='', allow_extra=False):
        self.name = name
        self.help = help
        self.allow_extra = allow_extra
        
    def mk_arg_parser (self, argp):
        return argp
        
    def run (self, args=None, extra=[]):
        return 0

    def name_out_file (self, in_file, args=None, work_dir=None):
        out_file = 'out'
        if work_dir is not None:
            out_file = os.path.join (work_dir, out_file)
        return out_file
        
    def main (self, argv):
        import argparse
        ap = argparse.ArgumentParser (prog=self.name, description=self.help)
        ap = self.mk_arg_parser (ap)
        
        if self.allow_extra:
            args, extra = ap.parse_known_args (argv)
        else:
            args = ap.parse_args (argv)
            extra = []
        return self.run (args, extra)
    
class LimitedCmd (CliCmd):
    def __init__ (self, name='', help='', allow_extra=False):
        super (LimitedCmd, self).__init__ (name, help, allow_extra)

    def mk_arg_parser (self, argp):
        argp = super(LimitedCmd, self).mk_arg_parser (argp)
        argp.add_argument ('--cpu', type=int, dest='cpu', metavar='SEC',
                           help='CPU time limit (seconds)', default=-1)
        argp.add_argument ('--mem', type=int, dest='mem', metavar='MB',
                           help='MEM limit (MB)', default=-1)
        return argp
        

class AgregateCmd (CliCmd):
    def __init__ (self, name='', help='', cmds=[]):
        super(AgregateCmd, self).__init__(name, help, allow_extra=True)
        self.cmds = cmds
    
    def mk_arg_parser (self, argp):
        sb = argp.add_subparsers ()
        for c in self.cmds:
            sp = sb.add_parser (c.name, help=c.help)
            sp = c.mk_arg_parser (sp)
            sp.set_defaults (func = c.run)
        return argp
            
    def run (self, args=None, extra=[]):
        return args.func (args, extra)
    
class SeqCmd (AgregateCmd):
    def __init__ (self, name='', help='', cmds=[]):
        super (SeqCmd, self).__init__ (name, help, cmds)

    def mk_arg_parser (self, ap):
        add_in_out_args (ap)
        ap.add_argument ('--save-temps', '--keep-temps',
                         dest="save_temps",
                         help="Do not delete temporary files",
                         action="store_true", default=False)
        ap.add_argument ('--temp-dir', dest='temp_dir', metavar='DIR',
                         help="Temporary directory", default=None)
        
        return ap
    
    def run (self, args, extra):
        res = 0
        in_file = args.in_file
        out_file = None
        
        work_dir = createWorkDir (args.temp_dir, args.save_temps, 'sea-')
        
        # all but last command
        for c in self.cmds[:-1]:
            argv = list()
            argv.extend (extra)
            out_file = c.name_out_file (in_file, args, work_dir)
            argv.extend (['-o', out_file])
            argv.append (in_file)
            res = c.main (argv)
            if res <> 0: return res

            in_file = out_file
            out_file = None
        
        # last command
        c = self.cmds [len (self.cmds) - 1]
        argv = list()
        argv.extend (extra)
        argv.extend (['-o', args.out_file])
        argv.append (in_file)
        res = c.main (argv)
        return res
    
class ExtCmd (LimitedCmd):
    def __init__ (self, name, help='', quiet=False):
        super (ExtCmd, self).__init__ (name, help, allow_extra=True)
        self.cmd = None
        self.quiet = quiet

    def run (self, args, extra):
        argv = [self.name]
        argv.extend (extra)
        
        if not self.quiet: print ' '.join (argv)
        
        self.cmd = TimeLimitedExec (argv, args.cpu, args.mem)
        return self.cmd.Run ()
    
    @property    
    def stdout (self): return self.cmd.stdout
        

        
