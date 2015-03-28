import os.path
import argparse


import util

class CliCmd (object):
    def __init__ (self, name='', allow_extra=False):
        self.name = name
        self.allow_extra = allow_extra
        
    def mk_arg_parser (self, argp):
        return argp
        
    def run (self, args=None, extra=[]):
        return 0

    def name_out_file (self, in_file, work_dir=None):
        out_file = 'out'
        if work_dir is not None:
            out_file = os.path.join (work_dir, out_file)
        return out_file
        
    def main (self, argv):
        import argparse
        ap = argparse.ArgumentParser ()
        ap = self.mk_arg_parser (ap)
        
        if self.allow_extra:
            args, extra = ap.parse_known_args (argv)
        else:
            args = ap.parse_args (argv)
            extra = []
        return self.run (args, extra)
    
class LimitedCmd (CliCmd):
    def __init__ (self, name=''):
        super (LimitedCmd, self).__init__ (name)

    def mk_arg_parser (self, argp):
        argp = super(LimitedCmd, self).mk_arg_parser (argp)
        argp.add_argument ('--cpu', type=int, dest='cpu', metavar='SEC',
                           help='CPU time limit (seconds)', default=-1)
        argp.add_argument ('--mem', type=int, dest='mem', metavar='MB',
                           help='MEM limit (MB)', default=-1)
        return argp
        

class AgregateCmd (CliCmd):
    def __init__ jself, name='', cmds=[]):
        super(AgregateCmd, self).__init__(name, allow_extra=True)
        self.cmds = cmds
    
    def mk_arg_parser (self, argp):
        sb = argp.add_subparsers ()
        for c in self.cmds:
            sp = sb.add_parser (c.name)
            sp = c.mk_arg_parser (sp)
            sp.set_defaults (func = lambda x, e : c.run (x, e))
        return argp
            
    def run (self, args=None, extra=[]):
        return args.func (args, extra)
    
class SeqCmd (AgregateCmd):
    def __init__ (self, name='', cmds=[]):
        super (SeqCmd, self).__init__ (name, cmds)

    def mk_arg_parser (self, ap):
        p.add_argument ('-o', dest='out_file',
                        metavar='FILE', help='Output file name', default=None)
        p.add_argument ('file', dest='in_file',
                        metavar='FILE', help='Input file')
        
        p.add_argument ("--save-temps", dest="save_temps",
                        help="Do not delete temporary files",
                        action="store_true",
                        default=False)
        p.add_argument ("--temp-dir", dest="temp_dir", metavar='DIR',
                        help="Temporary directory",
                        default=None)
        
        return ap
    
    def run (self, args, extra):
        res = 0
        in_file = args.in_file
        out_file = None
        
        work_dir = util.createWorkDir (args.temp_dir, args.save_temps, 'sea-')
        
        # all but last command
        for c in self.cmd[:-1]:
            argv = list()
            argv.extend (extra)
            out_file = cmd.name_out_file (in_file, work_dir)
            argv.extend (['-o', out_file])
            argv.append (in_file)
            res = c.main (argv)
            if res <> 0: return res

            in_file = out_file
            out_file = None
        
        # last command
        c = self.cmd [len (self.cmd) - 1]
        argv = list()
        argv.extend (extra)
        argv.extend (['-o', args.out_file])
        argv.append (in_file)
        res = c.main (argv)
        return res
    
class ExtCmd (LimitedCmd):
    def __init__ (self, name, quiet=False):
        super (ExtCmd, self).__init__ (name, allow_extra=True)
        self.cmd = None
        self.quiet = quiet

    def run (self, args, extra):
        argv = [self.name]
        argv.extend (extra)
        
        if not self.quiet: print argv.join (' ')
        
        self.cmd = util.TimeLimitedExec (argv, args.cpu, args.mem)
        return self.cmd.Run ()
    
    @property    
    def stdout (self): return self.cmd.stdout
        

        
