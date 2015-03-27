import os
import os.path

import threading
import subprocess


def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

def which(program):
    fpath, fname = os.path.split(program)
    if fpath:
        if isexec (program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            exe_file = os.path.join(path, program)
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
        self.verbose = verbose

    def run(self):
        def set_limits ():
            import resource as r    
            if self.cpu > 0:
                r.setrlimit (r.RLIMIT_CPU, [self.cpu, self.cpu])
            if self.mem > 0:
                mem_bytes = self.mem * 1024 * 1024
                r.setrlimit (r.RLIMIT_AS, [mem_bytes, mem_bytes])
                
        if self.verbose > 0: print self.cmd
        self.p = subprocess.Popen(self.cmd, 
                stdout=subprocess.PIPE,
                preexec_fn=set_limits)
        self.stdout, unused = self.p.communicate()

    def Run(self):
        self.start()

        if self.cpu > 0:
            self.join(self.cpu+5)
        else:
            self.join()

        if self.is_alive():
            print 'still alive, terminating'
            self.p.terminate()      
            self.join(5)

        if self.is_alive():
            print 'still alive after attempt to terminate, sending kill'
            self.p.kill()

        return self.p.returncode

