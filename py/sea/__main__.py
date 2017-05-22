import sys
import os
path = os.path.dirname(sys.modules[__name__].__file__)
path = os.path.join(path, '..')
sys.path.insert(0, path)

## update system PATH to location of the package
os.environ['PATH'] = path + os.pathsep + os.environ['PATH']

import sea
import sea.commands

cmds = [sea.commands.Clang(),
        sea.commands.Seapp(),
        sea.commands.MixedSem(),
        sea.commands.Seaopt(),
        sea.commands.Seahorn(),
        sea.commands.SeahornClp(),
        sea.commands.Smt,
        sea.commands.FrontEnd,
        sea.commands.Clp,
        sea.commands.feCrab,
        sea.commands.seaTerm,
        sea.commands.funcInfo,
        sea.commands.seaInc,
        sea.commands.feInspect]

cmd = sea.AgregateCmd('sea', cmds)
sys.exit (cmd.main (sys.argv[1:]))
