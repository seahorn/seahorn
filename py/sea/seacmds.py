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
        super (Clang, self).__init__('clang')
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
