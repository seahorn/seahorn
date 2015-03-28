import util
import CliCmd

import os.path

# remaps a file based on working dir and a new extension
def _remap_file_name (in_file, ext, work_dir):
    out_file = in_file
    if work_dir is not None:
        out_file = os.path.basename (in_file)
        out_file = os.path.join (work_dir, out_file)
    out_file = os.path.splitext (out_file)[0]
    out_file = out_file + ext
    return out_file
    
class Clang(CliCmd.LimitedCmd):
    def __init__ (self, quiet=False):
        super (Clang, self).__init__('clang', allow_extra=True)
        cmd_name = util.which (['clang-mp-3.6', 'clang-3.6', 'clang',
                                'clang-mp-3.5', 'clang-mp-3.4'])
        if cmd_name is None: raise IOError ('clang not found')
        self.clangCmd = CliCmd.ExtCmd (cmd_name)


    def mk_arg_parser (self, ap):
        ap = super (Clang, self).mk_arg_parser (ap)
        ap.add_argument ('-m', type=int, dest='machine',
                         help='Machine architecture MACHINE:[32,64]', default=32)
        ap.add_argument ('-g', default=False, action='store_true',
                         dest='debug_info', help='Compile with debug info')
        ap.add_argument ('-o', dest='out_file',
                         metavar='FILE', help='Output file name', default=None)
        ap.add_argument ('in_file',  metavar='FILE', help='Input file')
        return ap
    
    def name_out_file (self, in_file, work_dir=None):
        return _remap_file_name (in_file, '.bc', work_dir)
        
    def run (self, args, extra):
        argv = ['-c', '-emit-llvm']
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

class Seapp(CliCmd.LimitedCmd):
    def __init__(self, quiet=False):
        super(CliCmd, self).__init__('seapp', allow_extra=True)
        cmd_name = util.which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = CliCmd.ExtCmd (cmd_name)

    @property
    def stdout (self):
        return self.seappCmd.stdout
        
    def name_out_file (self, in_file, work_dir=None):
        return _remap_file_name (in_file, '.pp.bc', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seapp, self).mk_arg_parser (ap)
        ap.add_argument ('--inline', dest='inline', help='Inline all functions',
                         default=False, action='store_true')
        ap.add_argument ('-o', dest='out_file',
                         metavar='FILE', help='Output file name', default=None)
        ap.add_argument ('in_file',  metavar='FILE', help='Input file')
        return ap
    
    def run (self, args, extra):
        argv = list()
        if args.out_file is not None:
            argv.extend (['-o', args.out_file])
        if args.inline: argv.append ('--horn-inline-all')
        return self.seappCmd.run (args, argv)
        
class MixedSem(CliCmd.CliCmd):
    def __init__(self, quiet=False):
        super(CliCmd, self).__init__('seapp', allow_extra=True)
        cmd_name = util.which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = CliCmd.ExtCmd (cmd_name)

    @property
    def stdout (self):
        return self.seappCmd.stdout
        
    def name_out_file (self, in_file, work_dir=None):
        return _remap_file_name (in_file, '.ms.bc', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seapp, self).mk_arg_parser (ap)
        ap.add_argument ('--ms-skip', dest='ms_skip', help='Skip mixed semantics',
                         default=False, action='store_true')
        ap.add_argument ('-o', dest='out_file',
                         metavar='FILE', help='Output file name', default=None)
        ap.add_argument ('in_file',  metavar='FILE', help='Input file')
        return ap
    
    def run (self, args, extra):
        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if not args.ms_skip: argv.append ('--horn-mixed-sem')
        return self.seappCmd.run (args, argv)

class Seaopt(CliCmd.LimitedCmd):
    def __init__(self, quiet=False):
        super(CliCmd, self).__init__('seaopt', allow_extra=True)
        cmd_name = util.which (['seaopt', 'opt-mp-3.6', 'opt-3.6', 'opt'])
        if cmd_name is None: raise IOError ('niether seaopt nor opt where found')
        self.seaoptCmd = CliCmd.ExtCmd (cmd_name)

    @property
    def stdout (self):
        return self.seaoptCmd.stdout
        
    def name_out_file (self, in_file, work_dir=None):
        return _remap_file_name (in_file, '.o.bc', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seapp, self).mk_arg_parser (ap)
        ap.add_argument ('-O', type=int, dest='opt_level', metavar='INT',
                         help='Optimization level L:[0,1,2,3]', default=3)
        ap.add_argument ('-o', dest='out_file',
                         metavar='FILE', help='Output file name', default=None)
        ap.add_argument ('in_file',  metavar='FILE', help='Input file')
        return ap
    
    def run (self, args, extra):
        argv = ['-f', '-funit-at-a-atime']
        if args.out_file is not None:
            argv.extend (['-o', args.out_file])
        if args.opt_level > 0 && args.opt_level <= 3:
            argv.extend (['-O', str(args.opt_level)])
        return self.seappCmd.run (args, argv)
