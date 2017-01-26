#!/usr/bin/env python

import fractions
import sys
import time
import z3

from program import *
import stats

debug = False

def ranking(store,var):
    """ yields a list of ranking functions of the form
            m0 * var[0] + ... + mk * var[k] + q
        obtained from the points in store
    """
    # maximum number of ranking functions in the list
    def models(): return 1
    # least common multiple
    def lcm(a,b): return abs(a * b) // fractions.gcd(a,b)

    v = len(var)
    # unknown ranking function coefficients
    c = [z3.Real('m%d' % (i)) for i in range(v+1)]
    # unknown ranking function constant
    q = z3.Real('q')
    # z3 solver
    s = z3.Solver()
    s.reset()
    # adding rules to the solver (linear combinations of the points in store)
    rules = []
    for i in range(len(store)):
        r = sum([store[i][j]*c[j] for j in range(v)]) + q == store[i][v]
        rules.append(r)
        s.add(r)
    # getting the set of ranking functions
    functions = list()
    j = 0
    while s.check() == z3.sat and j < models():
        j = j + 1
        m = s.model()   # getting a model for a ranking function
        # print 'model:', m
        n = [0 for i in range(v+1)]
        d = [0 for i in range(v+1)]
        l = 1
        for i in range(v):
            k = m[c[i]]
            if k is not None:
                n[i] = k.numerator_as_long()
                d[i] = k.denominator_as_long()
                l = lcm(l,d[i])
        k = m[q]
        n[v] = k.numerator_as_long()
        d[v] = k.denominator_as_long()
        l = lcm(l,d[v])
        # building a single ranking function
        # (a rank 1/2 * x + 1/3 becomes 3 * x + 2)
        if n[v] != 0:
            rank = z3.IntSort().cast(n[v]*l/d[v])
        else:
            rank = z3.IntSort().cast(0)
        for i in range(v):
            if n[i] == 1 and (l/d[i]) == 1:
                rank += var[i]
            elif n[i] == -1 and (l/d[i]) == 1:
                rank -= var[i]
            elif n[i] != 0:
                rank += z3.IntSort().cast(n[i]*l/d[i]) * var[i]
        functions.append(rank)
        # asking z3 for a different model
        block = z3.Not(z3.And([x() == m[x] for x in m]))
        s.add(block)

    return functions

def piecewise(fp):
    # program CFG
    program = Program(fp)
    parameters = program.parameters[1:]
    variables = [z3.Var(i, sort) for (i,sort)
        in zip(list(range(len(parameters))),parameters)]
    arguments = program.arguments[1:]

    # loops identification
    loops = program.loops_identification()
    # proving termination...
    rank = dict()
    for node in loops:
        # ...for all loops involving each node
        if loops[node]:
            if debug: print '\nloop:', loops[node], '\n'
            loop = set([n for path in loops[node] for n in path])   # loop nodes
            entry = set([(n,node)
                for n in program.prev[node] - loop])  # entry edges
            edges = set([n for path in loops[node]
                for n in zip(path[:-1],path[1:])])  # loop edges
            # exit = set([(node,n)
            #     for n in program.next[node] - loop])  # exit edges
            exit = set([(i,n)
                for i in loop for n in program.next[i] - loop])  # exit edges

            bits = list()   # (potentially) terminating bits
            pieces = [[z3.IntSort().cast(0)]]    # candidate ranking functions
            bit = program.get_bit(entry,node,'max',pieces,edges,exit)
            while bit:
                bit[node][0][-len(pieces)] -= bit[node][-1][-len(pieces)]
                bits.append(bit[node][0][:len(bit[node][0])-len(pieces)+1])
                rankings = ranking(bits,variables)
                for i in range(len(bits)):
                    rankings = ranking(bits[:i+1],variables)
                if not rankings:
                    if debug: print
                    del bits[:-1]
                    rankings = ranking(bits,variables)
                if debug: print 'bit:', zip(arguments + ['-'
                    for component in pieces],bits[-1])
                pieces[0].extend(rankings)
                if debug: print 'pieces:', [[z3.substitute_vars(x,*arguments)
                    for x in component] for component in pieces]
                bit = program.get_bit(entry,node,'max',pieces,edges,exit)
            # check candidate ranking functions
            point = program.termination(entry,node,'max',pieces,edges,exit)
            pieces = [[z3.substitute_vars(x,*arguments)
                for x in component] for component in pieces]
            if point:
                rank[node] = (False,point)
                if debug: print '\nnon-terminating execution:', point
                if debug: print '(partial) loop ranking functions:', pieces
            else:
                rank[node] = (True,pieces)
                if debug: print '\nloop ranking functions:', pieces
    if debug: print '\nranking functions:', rank
    if all([r[0] for r in rank.values()]):
        stat("Result", "TRUE")
    else:
        stat("Result", "FALSE")

def lexicographic(fp):
    # program CFG
    program = Program(fp)
    parameters = program.parameters[1:]
    variables = [z3.Var(i, sort) for (i,sort)
        in zip(list(range(len(parameters))),parameters)]
    arguments = program.arguments[1:]

    # loops identification
    loops = program.loops_identification()
    # proving termination...
    rank = dict()
    for node in loops:
        # ...for all loops involving each node
        if loops[node]:
            if debug: print '\nloop:', loops[node]
            loop = set([n for path in loops[node] for n in path])   # loop nodes
            entry = set([(n,node)
                for n in program.prev[node] - loop])  # entry edges
            edges = set([n for path in loops[node]
                for n in zip(path[:-1],path[1:])])  # loop edges
            # exit = set([(node,n)
            #     for n in program.next[node] - loop])  # exit edges
            exit = set([(i,n)
                for i in loop for n in program.next[i] - loop])  # exit edges

            bits = list()   # (potentially) terminating bits
            pieces = [[z3.IntSort().cast(0)]]    # candidate ranking functions
            bit = program.get_bit(entry,node,'lex',pieces,edges,exit)
            while bit:
                bit[node][0][-len(pieces)] -= bit[node][-1][-len(pieces)]
                bits.append(bit[node][0][:len(bit[node][0])-len(pieces)+1])
                rankings = ranking(bits,variables)
                for i in range(len(bits)):
                    rankings = ranking(bits[:i+1],variables)
                if not rankings:
                    if debug: print
                    if debug: print 'bit:', zip(arguments + ['-'
                        for component in pieces],bits[-1])
                    bits = list()
                    rankings = [z3.IntSort().cast(0)]
                    pieces.insert(0,[])
                else:
                    if debug: print 'bit:', zip(arguments + ['-'
                        for component in pieces],bits[-1])
                del pieces[0][1:]
                pieces[0].extend(rankings)
                if debug: print 'pieces:', [[z3.substitute_vars(x,*arguments)
                        for x in component] for component in pieces]
                bit = program.get_bit(entry,node,'lex',pieces,edges,exit)
            # check candidate ranking functions
            point = program.termination(entry,node,'lex',pieces,edges,exit)
            pieces = [[z3.substitute_vars(x,*arguments)
                for x in component] for component in pieces]
            if point:
                rank[node] = (False,point)
                if debug: print 'non-terminating execution:', point
                if debug: print '(partial) loop ranking functions:', pieces
            else:
                rank[node] = (True,pieces)
                if debug: print 'loop ranking functions:', pieces
    if debug: print '\nranking functions:', rank
    if all([r[0] for r in rank.values()]):
        stat("Result", "TRUE")
        stat("Ranking-Function", rank)
    else:
        stat("Result", "FALSE")


def stat (key, val): stats.put (key, val)

def seaTerm(smt_file, rank_function):
    try:
        stat ('Result','UNKNOWN')
        stat ('Ranking_Function', rank_function)
        fp = z3.Fixedpoint()
        fp.set(engine='spacer')
        fp.set('xform.inline_eager', False)
        fp.set('xform.slice', False)
        fp.set('xform.inline_linear', False)
        fp.set('pdr.utvpi', False)
        fp.set('xform.karr', True)
        query = fp.parse_file(smt_file)
        with stats.timer('Termination'):
            if rank_function == 'max':
                piecewise(fp)
            elif rank_function == 'lex':
                lexicographic(fp)
            else:
                raise IOError('unknown ranking function template')
    except Exception as e:
        raise IOError(str(e))
    finally:
        stats.brunch_print()

def main(argv):
    fp = z3.Fixedpoint()
    fp.set(engine='spacer')
    fp.set('xform.inline_eager', False)
    fp.set('xform.slice', False)
    fp.set('xform.inline_linear', False)
    fp.set('pdr.utvpi', False)
    fp.set('xform.karr', True)
    query = fp.parse_file(argv[1])

    # proving termination...
    if len(argv) < 3:
        print 'please choose a ranking function template:'
        print '    max\t\t(piecewise)'
        print '    lex\t\t(lexicographic)'
    else:
        if argv[2] == 'max':
            # start = time.time()
            piecewise(fp)
            # end = time.time()
            # print 'Time: %.2fs' % (end - start)
        elif argv[2] == 'lex':
            # start = time.time()
            lexicographic(fp)
            # end = time.time()
            # print 'Time: %.2fs' % (end - start)
        elif argv[2] == 'mul':
            # start = time.time()
            multiphase(fp)
            # end = time.time()
            # print 'Time: %.2fs' % (end - start)
        else:
            print 'unknown ranking function template'

if __name__ == "__main__":
    main(sys.argv)
