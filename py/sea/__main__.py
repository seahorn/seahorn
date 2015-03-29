import sea
import sea.commands
import sys

cmds = [sea.commands.Clang(),
        sea.commands.Seapp(),
        sea.commands.MixedSem(),
        sea.commands.Seaopt(),
        sea.commands.Seahorn(),
        sea.commands.SeaGen ()]
        
    
cmd = sea.AgregateCmd('sea', cmds)
sys.exit (cmd.main (sys.argv[1:]))
