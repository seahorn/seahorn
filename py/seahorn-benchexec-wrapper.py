"""
SeaHorn Verification Framework
Copyright (c) 2015 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified BSD license, please see license.txt for full
terms.

DM-0002198
"""
import benchexec.util as util
import benchexec.tools.template

class Tool(benchexec.tools.template.BaseTool):

    def executable(self):
        return util.find_executable('sea_svcomp')


    def name(self):
        return 'SeaHorn-F16'

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        output = '\n'.join(output)
        if "BRUNCH_STAT Result TRUE" in output:
            status = "SAFE"
        elif "BRUNCH_STAT Result FALSE" in output:
            status = "UNSAFE"
        elif returnsignal == 9 or returnsignal == (128+9):
            if isTimeout:
                status = "TIMEOUT"
            else:
                status = "KILLED BY SIGNAL 9"
        elif returncode != 0:
            status = "ERROR ({0})".format(returncode)
        elif:
            status = 'FAILURE'
            
        return status
