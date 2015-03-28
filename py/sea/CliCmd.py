class CliCmd (object):
    def __init__ (self, name=""):
        self.name = name
        
    def mk_arg_parser (self, argp):
        return argp
        
    def run (self, args=None, extra=[]):
        return 0

    def main (self, argv):
        import argparse
        ap = argparse.ArgumentParser ()
        ap = self.mk_arg_parser (ap)
        
        args = ap.parse_args (argv)
        return self.run (args)
    
class LimitedCmd (CliCmd):
    def __init__ (self, name=""):
        super (LimitedCmd, self).__init__ (name)

    def mk_arg_parser (self, argp):
        argp = super(LimitedCmd, self).mk_arg_parser (argp)
        argp.add_argument ('--cpu', type=int, dest='cpu', metavar='SEC',
                           help='CPU time limit (seconds)', default=-1)
        argp.add_argument ('--mem', type=int, dest='mem', metavar='MB',
                           help='MEM limit (MB)', default=-1)
        return argp
        

class AgregateCmd (CliCmd):
    def __init__ (self, name='', cmds=[]):
        super(AgregateCmd, self).__init__(name)
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
        
    def main (self, argv):
        import argparse
        ap = argparse.ArgumentParser ()
        ap = self.mk_arg_parser (ap)
        
        args, extra = ap.parse_known_args (argv)
        return args.func (args, extra)
        
class ExtCmd (LimitedCmd):
    def __init__ (self, name):
        super (ExtCmd, self).__init__ (name)
        self.cmd = None

    def run (self, args, extra):
        argv = [self.name]
        argv.extend (extra)
        
        import util
        self.cmd = util.TimeLimitedExec (argv, args.cpu, args.mem, verbose=1)
        return self.cmd.Run ()
        
    def main (self, argv):
        import argparse
        ap = argparse.ArgumentParser ()
        ap = self.mk_arg_parser (ap)
        
        args, extra = ap.parse_known_args (argv)
        return self.run (args, extra)        
        

        
