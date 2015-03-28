import CliCmd
import seacmds
import sys

cmds = [seacmds.Clang(),
        seacmds.Seapp(),
        seacmds.MixedSem(),
        seacmds.Seaopt(),
        seacmds.Seahorn(),
        seacmds.SeaGen ()]
        
    
cmd = CliCmd.AgregateCmd('sea', cmds)
sys.exit (cmd.main (sys.argv[1:]))
