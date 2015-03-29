import sea 

import os.path

from sea import add_in_out_args, which

# remaps a file based on working dir and a new extension
def _remap_file_name (in_file, ext, work_dir):
    out_file = in_file
    if work_dir is not None:
        out_file = os.path.basename (in_file)
        out_file = os.path.join (work_dir, out_file)
    out_file = os.path.splitext (out_file)[0]
    out_file = out_file + ext
    return out_file


def _add_S_arg (ap):
    ap.add_argument ('-S', dest='llvm_asm', default=False, action='store_true',
                     help='Write output as LLVM assembly')
    return ap

class Clang(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (Clang, self).__init__('clang', allow_extra=True)
        self.clangCmd = None

    def mk_arg_parser (self, ap):
        ap = super (Clang, self).mk_arg_parser (ap)
        ap.add_argument ('-m', type=int, dest='machine',
                         help='Machine architecture MACHINE:[32,64]', default=32)
        ap.add_argument ('-g', default=False, action='store_true',
                         dest='debug_info', help='Compile with debug info')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def name_out_file (self, in_file, args=None, work_dir=None):
        ext = '.bc'
        if args.llvm_asm: ext = '.ll'
        return _remap_file_name (in_file, ext, work_dir)
        
    def run (self, args, extra):
        cmd_name = which (['clang-mp-3.6', 'clang-3.6', 'clang',
                                'clang-mp-3.5', 'clang-mp-3.4'])
        if cmd_name is None: raise IOError ('clang not found')
        self.clangCmd = sea.ExtCmd (cmd_name)
        
        argv = ['-c', '-emit-llvm']
        if args.llvm_asm: argv.append ('-S')
        if args.machine == 32: argv.extend (['-arch', 'i386'])
        elif args.machine == 64: argv.extend (['-arch', 'x86_64'])
        
        if args.debug_info: argv.append ('-g')
        if args.out_file is not None:
            argv.extend (['-o', args.out_file])
        argv.append (args.in_file)
        return self.clangCmd.run (args, argv)

    @property
    def stdout (self):
        return self.clangCmd.stdout

class Seapp(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(Seapp, self).__init__('pp', allow_extra=True)
        
    @property
    def stdout (self):
        return self.seappCmd.stdout
        
    def name_out_file (self, in_file, args=None, work_dir=None):
        ext = '.pp.bc'
        if args.llvm_asm: ext = '.pp.ll'
        return _remap_file_name (in_file, ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seapp, self).mk_arg_parser (ap)
        ap.add_argument ('--inline', dest='inline', help='Inline all functions',
                         default=False, action='store_true')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name)
        
        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if args.inline: argv.append ('--horn-inline-all')
        argv.append (args.in_file)
        return self.seappCmd.run (args, argv)
        
class MixedSem(sea.CliCmd):
    def __init__(self, quiet=False):
        super(MixedSem, self).__init__('ms', allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout
        
    def name_out_file (self, in_file, args=None, work_dir=None):
        ext = '.ms.bc'
        if args.llvm_asm: ext = '.ms.ll'
        return _remap_file_name (in_file, ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (MixedSem, self).mk_arg_parser (ap)
        ap.add_argument ('--ms-skip', dest='ms_skip', help='Skip mixed semantics',
                         default=False, action='store_true')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name)
        
        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if not args.ms_skip: argv.append ('--horn-mixed-sem')
        argv.append (args.in_file)
        return self.seappCmd.run (args, argv)

class Seaopt(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(Seaopt, self).__init__('opt', allow_extra=True)

    @property
    def stdout (self):
        return self.seaoptCmd.stdout
        
    def name_out_file (self, in_file, args, work_dir=None):
        ext = 'o{0}.bc'.format(args.opt_level)
        if args.llvm_asm: ext = 'o{0}.ll'.format(args.opt_level)
        return _remap_file_name (in_file, ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seaopt, self).mk_arg_parser (ap)
        ap.add_argument ('-O', type=int, dest='opt_level', metavar='INT',
                         help='Optimization level L:[0,1,2,3]', default=3)
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def run (self, args, extra):
        cmd_name = which (['seaopt', 'opt-mp-3.6', 'opt-3.6', 'opt'])
        if cmd_name is None: raise IOError ('niether seaopt nor opt where found')
        self.seaoptCmd = sea.ExtCmd (cmd_name)

        argv = ['-f', '-funit-at-a-atime']
        if args.out_file is not None:
            argv.extend (['-o', args.out_file])
        if args.opt_level > 0 and args.opt_level <= 3:
            argv.extend (['-O', str(args.opt_level)])
        argv.append (args.in_file)
        return self.seappCmd.run (args, argv)

class Seahorn(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (Seahorn, self).__init__ ('horn', allow_extra=True)
        
    @property
    def stdout (self):
        return self.seahornCmd.stdout

    def name_out_file (self, in_file, args=None, work_dir=None):
        return _remap_file_name (in_file, '.smt2', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seahorn, self).mk_arg_parser (ap)
        add_in_out_args (ap)
        ap.add_argument ('--cex', dest='cex', help='Destination for a cex',
                         default=None, metavar='FILE')
        ap.add_argument ('--solve', dest='solve', action='store_true',
                         help='Solve', default=False)
        ap.add_argument ('--ztrace', dest='ztrace', metavar='STR',
                         default=None, help='Z3 trace levels')
        ap.add_argument ('--verbose', '-v', dest='verbose', type=int, default=0,
                         help='Verbosity level', metavar='N')
        ap.add_argument ('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        ap.add_argument ('--oll', dest='asm_out_file', default=None,
                         help='LLVM assembly output file')
        ### TODO: expose options for semantic level, inter-procedural
        ### encoding, step, flat, etc.
        return ap
    def _is_seahorn_opt (x):
        if x.startswith ('-'):
            y = x.strip ('-')
            return y.startswith ('horn') or y.startswith ('ikos') or y.startswith ('log')
        return False

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seahornCmd = sea.ExtCmd (cmd_name)
        
        argv = list()
        if args.solve:
            argv.append ('-horn-solve')
        if args.cex is not None and args.solve:
            argv.append ('-horn-cex')
            argv.append ('--honr-svcomp-cex={0}'.format (cex))
            argv.extend (['-log', 'cex'])
        if args.asm_out_file is not None: argv.extend (['-oll', args.asm_out_file])
        
        argv.extend (['-horn-inter-proc', '-horn-sem-lvl=mem', '-horn-step=large'])
        
        if args.verbose > 0: argv.extend (['-zverbose', str(args.verbose)])

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        if args.ztrace is not None:
            for l in args.ztrace.split (':'): argv.extend (['-ztrace', l])
        
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        argv.append (args.in_file)
        
        # pick out extra seahorn options
        argv.extend (filter (_is_seahorn_opt, extra))
        
            
        return seahornCmd.run (args, argv)

class SeaGen(sea.SeqCmd):
    def __init__(self):
        cmds = [Clang (),
                Seapp (),
                MixedSem (),
                Seaopt (),
                Seahorn ()]
        super(SeaGen, self).__init__ ('gen', cmds)
    
