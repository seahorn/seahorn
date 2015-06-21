import z3
import z3core

def nnf (e): return z3.Tactic ('nnf').apply (e)

def bitblast (e):
  ctx = e.ctx
  goal = z3.Goal (ctx=ctx)
  goal.add (z3.simplify (e))
  tactic = z3.Tactic ('bit-blast', ctx=ctx)
  res = tactic.apply (goal, blast_full=True)
  assert (len (res) == 1)
  return res [0].as_expr ()

def extend (v1, v2):
  """extend AstVector v1 with elements from AstVector v2"""
  for x in v2: v1.push (x)

def pushed_solver (solver):
  """
  Context Manager helper to push a solver.

  s = Solver ()
  s.add (c1)
  # at this point s is not yet pushed
  with pushed_solver (s) as ps:
    # here ps is s after a push
    ps.add (c2)
    ps.add (c3)
    print ps
  # here s is just like it was before the 'with' statement
  print s
  """
  class PushSolverContextManager (object):
    def __init__ (self, solver):
      self.solver = solver

    def __enter__(self):
      self.solver.push ()
      return self.solver

    def __exit__ (self, exc_type, exc_value, traceback):
      self.solver.pop ()
      # do not suppress any exception
      return False

  return PushSolverContextManager (solver)

def mk_nary (op_fn, base, *args):
  """
  mk_nary (z3.And, mk_true(ctx), *args)
  """
  if len (args) == 0: return base
  if len (args) == 1: return args [0]
  print "here"
  return op_fn (*args)

def mk_true (ctx=None): return z3.BoolVal (True, ctx)
def mk_false (ctx=None): return z3.BoolVal (False, ctx)

def z3key (d) :
  """Return a key corresponding to d that can be safely used in
dictionaries

  """
  return d.ast.value

def z3AstRefKey (d) :
  return d.ast.value

def conjuncts (exp) :
  assert z3.is_bool (exp)
  if z3.is_and (exp) :
    for i in range (exp.num_args ()) :
      yield exp.arg (i)
  else : yield exp

def get_conjuncts (exp) :
  assert z3.is_bool (exp)
  if z3.is_and (exp) : return exp.children ()
  else : return [exp]

def getFirstConjunct (exp) :
  assert z3.is_app (exp)
  if z3.is_and (exp) : return exp.arg (0)
  else : return exp

def z3ExpChildGenerator (exp) :
  if z3.is_app (exp) :
    for i in range (exp.num_args ()) :
      yield exp.arg (i)

def z3_translate (x, ctx):
  """ A version of z3.AstRef.translate that handles sorts and function declarations correctly"""
  if x.ctx == ctx: return x
  if isinstance (x, z3.BoolSortRef): return z3.BoolSort (ctx)
  if z3.is_arith_sort (x):
    if x.is_int (): return z3.IntSort (ctx)
    else :
      assert x.is_real ()
      return z3.RealSort (ctx)
  if isinstance (x, z3.FuncDeclRef):
    sorts = [z3_translate (x.domain (i), ctx) for i in range (decl.arity ())]
    sorts.append (z3_translate (x.range (), ctx))
    return z3.Function (x.name (), *sorts)

  return x.translate (ctx)

def createZ3Sort (sort_kind, z3ctx) :
  if sort_kind == z3.Z3_BOOL_SORT :
    return z3.BoolSort (ctx=z3ctx)
  elif sort_kind == z3.Z3_REAL_SORT :
    return z3.RealSort (ctx=z3ctx)
  elif sort_kind == z3.Z3_INT_SORT :
    return z3.IntSort (ctx=z3ctx)
  else :
    raise Exception ('Unsupported Sort')

def z3_flatten_exp (z3exp) :
  return z3.simplify (z3exp, flat=True,
                      # don't care about other options,
                      # which are true by default...
                      algebraic_number_evaluator=False,
                      bit2bool=False,
                      elim_sign_ext=False,
                      hi_div0=False,
                      mul_to_power=False,
                      push_to_real=False)

def is_implies (expr):
  return z3.is_app_of (expr, z3.Z3_OP_IMPLIES)

def isZ3Implies (expr) :
  return is_implies (expr)

def is_uninterpreted (decl):
  return decl.kind () == z3.Z3_OP_UNINTERPRETED

def mk_forall (vars, body):
  if len (vars) > 0: return z3.ForAll (vars, body)
  return body

def z3ForAll (fvs, matrix) :
  return mk_forall (fvs, matrix)

def bound_var_name (quant, var):
  if z3.is_var (var):
    var = z3.get_var_index ()
  return quant.var_name (quant.num_vars () - 1 - var)

def bound_var_sort (quant, var):
  if z3.is_var (var):
    var = z3.get_var_index ()
  return quant.var_sort (quant.num_vars () - 1 - var)


class HelperBase(object):
  def __init__ (self, ctx=None):
    self._ctx = ctx
    self._true = mk_true (ctx)
    self._false = mk_false (ctx)

  @property
  def ctx (self): return self._ctx
  @property
  def true (self): return self._true
  @property
  def false (self): return self._false


  def mk_and (self, *args): return mk_nary (z3.And, self.true, *args)
  def mk_or (self, *args): return mk_nary (z3.Or, self.false, *args)


class Substitute (object):
  def __init__ (self, *m):
    if isinstance (m, tuple):
      m1 = z3._get_args (m)
      if isinstance (m1, list):
        m = z3._get_args (m1)

    ## keep a pointer to the substitution map so that it
    ## is not garbage collected
    self._sub = m

    ## prepare arguments for a call to substitute
    self._num = len (m)
    self._from = (z3.Ast * self._num) ()
    self._to = (z3.Ast * self._num) ()
    for i in range (self._num):
      self._from[i] = m[i][0].as_ast ()
      self._to[i] = m[i][1].as_ast ()

  def apply (self, expr):
    res = z3core.Z3_substitute (expr.ctx.ref (), expr.as_ast (),
                                self._num, self._from, self._to)

    ## assume that substitution does not change the class of the expression
    return expr.__class__ (res, expr.ctx)

  def __call__ (self, t): return self.apply (t)


def substitute (t, *m):
  """ Re-implementation of z3.substitute """
  #return z3.substitute (t, *m)
  r = Substitute (*m)
  res = r.apply (t)

  # sanity check
  assert res.eq (z3.substitute (t, *m))
  return res

class SubstituteVars (object):
  def __init__ (self, *m):
    self._m = m
    self._num = len (m)
    self._to = (z3.Ast * self._num) ()
    for i in range (self._num):
      self._to [i] = m[i].as_ast ()

  def apply (self, t):
    res = z3core.Z3_substitute_vars (t.ctx.ref (), t.as_ast (),
                                     self._num, self._to)
    return t.__class__ (res, t.ctx)

  def __call__ (self, t): return self.apply (t)

def substitute_vars (t, *m):
  rw = SubstituteVars (*m)
  res = rw (t)
  assert res.eq (z3.substitute_vars (t, *m))
  return res

class MkExists (object):
  def __init__ (self, vs):
    if z3.is_app (vs):
      vs = [vs]

    self._saved_vs = vs
    self._num_vars = len (vs)

    num_vars = self._num_vars

    self._vs = (z3.Ast * num_vars) ()
    for i in range (num_vars):
      self._vs [i] = vs[i].as_ast ()

    self._pats = (z3.Pattern * 0) ()
    self._num_pats = 0

    self._num_no_pats = 0
    self._no_pats = (z3.Ast * 0) ()

  def apply (self, body):
    ctx = body.ctx
    qid = z3.to_symbol ("", ctx)
    skid = qid

    res = z3core.Z3_mk_quantifier_const_ex (ctx.ref (), False,
                                            1, qid, skid,
                                            self._num_vars, self._vs,
                                            self._num_pats, self._pats,
                                            self._num_no_pats, self._no_pats,
                                            body.as_ast ())
    return z3.QuantifierRef (res, ctx)

  def __call__ (self, body):
    return self.apply (body)

def Exists (vs, body):
  exists = MkExists (vs)
  res = exists (body)
  assert res.eq (z3.Exists (vs, body))
  return res

def find_atomic_terms (exp, terms = list (), seen = set ()):
  """ Finds all declarations in an expression """

  if (z3.is_quantifier (exp)):
    return find_atomic_terms (exp.body (), terms, seen)

  if not (z3.is_app (exp)) : return terms

  if z3AstRefKey (exp) in seen: return terms

  seen.add (z3AstRefKey (exp))
  decl = exp.decl ()

  # atomic term
  if decl.kind () == z3.Z3_OP_UNINTERPRETED:
    if z3AstRefKey (decl) not in seen:
      seen.add (z3AstRefKey (decl))
      terms.append (decl)
  # uninterpreted can also have kids
  for k in exp.children (): find_atomic_terms (k, terms, seen)
  return terms

import sys
def iterable_to_smtlib (v, out=sys.stdout):
  """ Print a sequence of SMTLIB2 formulas with declarations """
  terms = list ()
  seen = set ()
  for x in v: find_atomic_terms (x, terms, seen)
  for t in terms:
    out.write (t.sexpr ())
    out.write ('\n')
  for x in v:
    out.write ("(assert ")
    out.write (x.sexpr ())
    out.write (")\n")
  out.flush ()

def to_smtlib (exp, out=sys.stdout):
  """ Print formula in SMTLIB2 format with declarations """
  try:
    i = iter (exp)
    return iterable_to_smtlib (exp, out)
  except TypeError:
    return iterable_to_smtlib ([exp], out)

def solver_to_smtlib (solver, out=sys.stdout):
  to_smtlib (solver.assertions (), out)

qb_counter=0

def stripQuantifierBlock (expr) :
  """ strips the outermost quantifier block in a given expression and returns
  the pair (<list of consts replacing free vars>,
  <body with consts substituted for de-bruijn variables>)

  Example:

  assume expr.is_forall ()
  vars, body = strip_quantifier (expr)
  qexpr = z3.ForAll (vars, body)
  assert qexpr.eq (expr)
  """
  if not z3.is_quantifier (expr) : return ([], expr)
  global qb_counter
  z3ctx = expr.ctx
  consts = list ()
  # outside-in order of variables; z3 numbers variables inside-out but
  # substitutes outside-in
  for i in reversed (range (expr.num_vars ())) :
    v_name = expr.var_name (i) + "!" + str(qb_counter)
    qb_counter+=1
    v_sort = expr.var_sort (i)
    consts.append (z3.Const (v_name, z3_translate (v_sort, z3ctx)))
  matrix = z3.substitute_vars (expr.body (), *consts)
  return (consts, matrix)


###  TEME TODO
###  if e is equality and e.arg(0) is not:
###      a0 = e.arg (0).arg (0)
###      a1 = nnf (Not (e.arg (1)))
###
###  if e is (or !a b c d) then e = (=> a (or b c d))
