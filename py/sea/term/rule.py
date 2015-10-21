
import z3

class Rule:
    """ Rule """
    def var_name(self,rule,i):
        """ yields the name of a variable """
        if z3.is_var(i): i = z3.get_var_index()
        # (variables are numbered backwards within the predicates)
        return rule.var_name(rule.num_vars()-1-i)

    def var_sort(self,rule,i):
        """ yields the sort of a variable """
        if z3.is_var(i): i = z3.get_var_index()
        # (variables are numbered backwards within the predicates)
        return rule.var_sort(rule.num_vars()-1-i)

    def __init__(self,rule):
        """ unpacks a rule of the kind
             (I) z3.Forall(variables, head)
            or
            (II) z3.Forall(variables, z3.Implies(z3.And([tail,children]),head))
        """
        self.rule = rule        # original rule
        self.variables = None   # quantified variables
        self.predicate = None   # predicate declaration: name(pc,...)
        self.tail = None        # body predicate 
        self.children = None    # other body elements
        self.head = None        # head predicate
        # the rule is a z3 quantifier
        if z3.is_quantifier(rule):
            # quantified variables
            self.variables = list()
            for i in range(rule.num_vars()):
                sort = self.var_sort(rule,i).kind()
                if sort == z3.Z3_INT_SORT:
                    self.variables.append(z3.Int(self.var_name(rule,i)))
                elif sort == z3.Z3_BOOL_SORT:
                    self.variables.append(z3.Bool(self.var_name(rule,i)))
                else:
                    raise ValueError('unsopported sort:',sort)
            # unpacks the rule body
            head = rule.body()
            if z3.is_app_of(head,z3.Z3_OP_IMPLIES):
                # the rule is of kind (II)
                body = head.arg(0)  # z3.Implies body
                if z3.is_app_of(body,z3.Z3_OP_AND):
                    # unpacks the other body elements
                    # (assumes single uninterpreted predicate in body)
                    self.children = list()
                    for c in body.children():
                        child = z3.substitute_vars(c,*self.variables)
                        # unpacks the body predicate 
                        if z3.is_app_of(child,z3.Z3_OP_UNINTERPRETED) \
                            and self.tail is None:  
                                self.tail = child   # body predicate
                        else:
                            self.children.append(child)
                else:
                    raise ValueError('unsupported implication body:',body)
                head = head.arg(1)  # z3.Implies head
            if z3.is_app_of(head,z3.Z3_OP_UNINTERPRETED):
                # the rule is of kind (I)
                name = head.decl().name()   # predicate name
                parameters = list()         # predicate parameters
                arguments = list()          # predicate arguments
                for i in range(head.num_args()):
                    arg = head.arg(i)
                    parameters.append(arg.sort())
                    arguments.append(z3.substitute_vars(arg,*self.variables))
                parameters.append(z3.BoolSort())
                self.predicate = z3.Function(name,*parameters)
                self.head = self.predicate(*arguments)  # head predicate
            else:
                raise ValueError('unsupported rule body:',body)
        
    def __repr__(self):
        if self.tail is not None:
            return 'z3.Forall(%s, z3.Implies(z3.And([%s,%s]), %s))' \
                % (self.variables,self.tail,self.children,self.head)
        else:
            return 'z3.Forall(%s, %s)' % (self.variables,self.head)

    def __str__(self):
        if self.tail is not None:
            return 'z3.Forall(%s, z3.Implies(z3.And([%s,%s]), %s))' \
                % (self.variables,self.tail,self.children,self.head)
        else:
            return 'z3.Forall(%s, %s)' % (self.variables,self.head)
    
    def parameters(self):
        parameters = list()
        for i in range(self.predicate.arity()):
            parameters.append(self.predicate.domain(i))
        return parameters
    
    def head_args(self):
        arguments = list()
        for i in range(self.predicate.arity()):
            arguments.append(self.head.arg(i))
        return arguments
    
    def is_initial(self):
        """ tests if the rule is of kind (I), initial rule """
        return self.tail is None
            
    def head_pc(self,pc=None):
        """ modifies/yields the head pc """
        if pc:
            name = self.predicate.name()
            parameters = [z3.IntSort()]
            arguments = [z3.IntSort().cast(pc)]
            for i in range(1,self.predicate.arity()):
                parameters.append(self.predicate.domain(i))
                arguments.append(self.head.arg(i))
            parameters.append(z3.BoolSort())
            self.predicate = z3.Function(name,*parameters)
            self.head = self.predicate(*arguments)
        else:
            return self.head.arg(0)
    
    def tail_pc(self,pc=None):
        """ modifies/yields the tail pc (assumes the rule is of kind (II)) """
        if pc:
            name = self.predicate.name()
            parameters = [z3.IntSort()]
            arguments = [z3.IntSort().cast(pc)]
            for i in range(1,self.predicate.arity()):
                parameters.append(self.predicate.domain(i))
                arguments.append(self.tail.arg(i))
            parameters.append(z3.BoolSort())
            self.predicate = z3.Function(name,*parameters)
            self.tail = self.predicate(*arguments)
        else:
            return self.tail.arg(0)
    
    def is_entry(self,entry):
        """ tests if the rule is an entry rule """
        if self.tail is not None:   # the rule is of kind (II)
            # (tail predicate pc,head predicate pc) is an entry edge
            return (self.tail_pc().as_long(),self.head_pc().as_long()) in entry
        else:   # the rule is of kind (I)
            return False

    def is_loop(self,loop):
        """ tests if the rule is a loop rule """
        if self.tail is not None:   # the rule is of kind (II)
            # (tail predicate pc,head predicate pc) is a loop edge
            return (self.tail_pc().as_long(),self.head_pc().as_long()) in loop
        else:   # the rule is of kind (I)
            return False
    
    def is_exit(self,exit):
        """ tests if the rule is an exit rule """
        if self.tail is not None:   # the rule is of kind (II)
            # (tail predicate pc,head predicate pc) is an exit edge
            return (self.tail_pc().as_long(),self.head_pc().as_long()) in exit
        else:   # the rule is of kind (I)
            return False
    
    def add_vars(self,r,rr=None):
        """ adds a list of variables to the head (and tail) predicates """
        self.variables.extend(r)
        if self.tail is not None:   # the rule is of kind (II)
            name = self.predicate.name()
            parameters = list()
            tail_arguments = list()
            head_arguments = list()
            for i in range(self.predicate.arity()):
                parameters.append(self.predicate.domain(i))
                tail_arguments.append(self.tail.arg(i))
                head_arguments.append(self.head.arg(i))
            parameters.extend([x.sort() for x in r])
            tail_arguments.extend(r)
            if rr is not None:
                head_arguments.extend(rr)
                self.variables.extend(rr)
            else:
                head_arguments.extend(r) 
            parameters.append(z3.BoolSort())
            self.predicate = z3.Function(name,*parameters)
            self.tail = self.predicate(*tail_arguments)
            self.head = self.predicate(*head_arguments)
        else:
            name = self.predicate.name()
            parameters = list()
            head_arguments = list()
            for i in range(self.predicate.arity()):
                parameters.append(self.predicate.domain(i))
                head_arguments.append(self.head.arg(i))
            parameters.extend([x.sort() for x in r])
            head_arguments.extend(r)
            parameters.append(z3.BoolSort())
            self.predicate = z3.Function(name,*parameters)
            self.head = self.predicate(*head_arguments)

    def add_children(self,child):
        """ adds a list of children to the other body elements """
        if self.tail is not None:
            self.children.extend(child)
    
    def add_rank(self,r,rank,rr):
        """ adds a ranking function counter(s) initialization """
        self.add_vars(r,rr)
        self.add_children([x == rk for (x,rk) in zip(rr,rank)])
    
    def add_decrease(self,kind,r,rank,rr):
        """ adds a strict decrease for the ranking function counter(s) """
        if kind == 'mul':
            r.reverse()
            rr.reverse()
        self.add_vars(r,rr)
        
        if kind == 'mul':
            children = list()
            for i in range(len(rr)):

                nxt = [x < 0 for x in r[i+1:]]
                if nxt:
                    children.append(rr[i] == 
                        z3.If(z3.And(nxt),r[i] - 1,rank[i]))
                else:
                    children.append(rr[i] == r[i] - 1)
        else:
            nxt = [x < 0 for x in r[1:]]
            if nxt:
                children = [rr[0] == z3.If(z3.And(nxt),r[0] - 1,r[0])]
            else:
                children = [rr[0] == r[0] - 1]
            for i in range(1,len(rr)):
                nxt = [x < 0 for x in r[i+1:]]
                if nxt:
                    dcr = z3.If(z3.And(nxt),r[i] - 1,r[i])
                else:
                    dcr = r[i] - 1
                children.append(rr[i] == 
                    z3.If(z3.And([r[i] < 0]+nxt),rank[i],dcr))
        
        self.add_children(children)
    
    def add_bound(self,kind,r):
        """ adds a bounded condition for the ranking function counter(s) """
        if kind == 'mul': r.reverse()
        self.add_vars(r)
        self.add_children([r[0] < 0])
    