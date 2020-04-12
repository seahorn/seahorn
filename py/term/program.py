
import z3

from .rule import *

class Program:
    """ Program """
    def __init__(self,fp):        
        """ builds the program control flow graph (CFG) """
        # program rules and variables
        self.rules = list()
        seen, self.variables = set(), list()
        for rule in fp.get_rules():
            r = Rule(rule)
            if r.head is None: continue     # spurious rule
            self.rules.append(r)
            for x in r.variables:
                if x.hash() not in seen:
                    seen.add(x.hash())
                    self.variables.append(x)
        # program CFG
        self.prev = dict()
        self.next = dict()
        for r in self.rules:
            head = r.head_pc().as_long()
            if head not in self.__next__:
                self.next[head] = set()
            if head not in self.prev:
                self.prev[head] = set() 
            if r.is_initial():
                self.entry = head
                self.parameters = r.parameters()
                self.arguments = r.head_args()
            else:
                tail = r.tail_pc().as_long()
                self.prev[head].add(tail)
                self.next[tail].add(head)
        # print 'prev:', self.prev
        # print 'next:', self.next
        
    def loop_identification(self,pc):
        """ identifies all paths within the (natural) loop of pc """
        # (variant of) depth first search
        paths = list()
        stack = [(pc,[pc])]
        while stack:
            node,path = stack.pop()
            for nxt in self.next[node] - set(path[1:]):
                if nxt == pc:
                    paths.append(path)
                else:
                    stack.append((nxt,path + [nxt]))
        return paths
        
    def loops_identification(self):
        """ identifies all (natural) loops """
        # depth first search
        seen = set()
        loops = dict()
        stack = [self.entry]
        while stack:
            n = stack.pop()
            loops[n] = list()
            paths = self.loop_identification(n)
            for path in paths:
                s = str(sorted(path))
                if s not in seen:
                    seen.add(s)
                    loops[n].append(path + [n])
            stack.extend(self.next[n] - set(loops.keys()))
        return loops
    
    def get_bit(self,entry,header,kind,pieces,loop,exit):
        """ instruments the program rules with a ranking function
            in order to extract a TERMINATING execution
            such that rank is negative at loop exit
        """
        def mx(rankings):
            """ builds a MAX combination of a list of ranking functions """
            if len(rankings) <= 1:
                return rankings[0]
            else:
                r = mx(rankings[1:])
                return z3.If(rankings[0] < r,r,rankings[0])
        # new z3.Fixedpoint object
        fp = z3.Fixedpoint()
        fp.set(engine='spacer')
        fp.set('xform.inline_eager', False)
        fp.set('xform.slice', False)
        fp.set('xform.inline_linear', False)
        fp.set('pdr.utvpi', False)
        # fp.set('timeout',1000)
        # variable declarations
        for x in self.variables:
            fp.declare_var(x)
        # ranking function counter
        components = len(pieces)
        R = [z3.Int('R%d' % i) for i in range(components)]
        for component in R: fp.declare_var(component)
        RR = [z3.Int('RR%d' % i) for i in range(components)]
        for component in RR: fp.declare_var(component)
        # modifying and adding rules
        for rule in self.rules:
            r = Rule(rule.rule)
            if r.is_entry(entry):
                # ranking function(s) initialization before the loop
                rank = [[z3.substitute_vars(x,*r.head_args()[1:]) 
                    for x in component] for component in pieces]
                r.add_rank(R,[mx(component) for component in rank],RR)
                fp.register_relation(r.predicate)
            elif r.is_loop(loop):
                # ranking function(s) strict decrease within the loop
                rank = [[z3.substitute_vars(x,*r.head_args()[1:]) 
                    for x in component] for component in pieces]
                r.add_decrease(kind,R,[mx(component) for component in rank],RR)
            elif r.is_exit(exit):
                r.add_vars(R)
                # ranking function(s) boundedness from below after the loop
                q = Rule(rule.rule)
                q.add_bound(kind,R)
                q.head_pc(-1)
                fp.rule(q.head,[q.tail] + q.children)
                # query
                query = z3.Exists(q.variables,q.head)
            else:
                r.add_vars(R)
                # print 'NONE:', r
            # adding modified rules
            if r.tail is None:
                fp.rule(r.head)
            else:
                body = [r.tail] + r.children
                fp.rule(r.head,body)
        # querying for terminating execution with negative ranking function
        bit = dict()
        result = fp.query(query)
        if result == z3.sat:
            answer = fp.get_ground_sat_answer()
            children = answer.children()
            # print 'CHILDREN:\n', children
            bit = dict()
            for child in children:
                if child.children():    # some predicate might not have values
                    values = [x.as_long() for x in child.children()]
                    if values[0] not in bit:
                        bit[values[0]] = [values[1:]]
                    else:
                        bit[values[0]].insert(0,values[1:])
            # adding the first child to loop header to ensure progress 
            # (when the source of exit edges is not the loop header)
            first = [child for child in children if child.children()][0]
            values = [x.as_long() for x in first.children()]
            if header not in bit:
                bit[header] = [values[1:]]
            else:
                bit[header].append(values[1:])
            return bit
        else:
            return bit
    
    def termination(self,entry,header,kind,pieces,loop,exit):
        """ instruments the rules in fp with a ranking function 
            in order to extract a NON-TERMINATING execution
            such that rank is negative within the loop
        """
        def mx(rankings):
            """ builds a MAX combination of a list of ranking functions """
            if len(rankings) <= 1:
                return rankings[0]
            else:
                r = mx(rankings[1:])
                return z3.If(rankings[0] < r,r,rankings[0])
        # new z3.Fixedpoint object
        fp = z3.Fixedpoint()
        fp.set(engine='spacer')
        fp.set('xform.inline_eager', False)
        fp.set('xform.slice', False)
        fp.set('xform.inline_linear', False)
        fp.set('pdr.utvpi', False)
        # fp.set('timeout',1000)
        # variable declarations
        for x in self.variables:
            fp.declare_var(x)
        # ranking function counter
        components = len(pieces)
        R = [z3.Int('R%d' % i) for i in range(components)]
        for component in R: fp.declare_var(component)
        RR = [z3.Int('RR%d' % i) for i in range(components)]
        for component in RR: fp.declare_var(component)
        # modifying and adding rules
        for rule in self.rules:
            r = Rule(rule.rule)
            if r.is_entry(entry):
                # ranking function(s) initialization before the loop
                rank = [[z3.substitute_vars(x,*r.head_args()[1:]) 
                    for x in component] for component in pieces]
                r.add_rank(R,[mx(component) for component in rank],RR)
                fp.register_relation(r.predicate)
                # print 'ENTRY:', r
            elif r.is_loop(loop):
                # ranking function(s) strict decrease within the loop
                rank = [[z3.substitute_vars(x,*r.head_args()[1:]) 
                    for x in component] for component in pieces]
                r.add_decrease(kind,R,[mx(component) for component in rank],RR)
                # print 'LOOP:', r
                # ranking function(s) boundedness from below within the loop
                q = Rule(rule.rule)
                q.add_bound(kind,R)
                q.head_pc(-1)
                fp.rule(q.head,[q.tail] + q.children)
                # print 'EXIT:', q
                # query
                query = z3.Exists(q.variables,q.head)
            else:
                r.add_vars(R)
                # print 'NONE:', r
            # adding modified rules
            if r.tail is None:
                fp.rule(r.head)
            else:
                fp.rule(r.head,[r.tail] + r.children)
        # print '\nFP:', fp
        # querying for non-terminating execution
        result = fp.query(query)
        if result == z3.sat:
            answer = fp.get_ground_sat_answer()
            first = answer.children()[-2]
            point = [x.as_long() for x in first.children()[1:-1]]
            return list(zip(self.arguments[1:],point))
        else:
            return []
