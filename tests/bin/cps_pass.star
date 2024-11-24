def main():
  def cps(x):
    # we don't bake until we get to the goto
    # we may know the value of x statically
    # but we also may not
    # we could enforce compile time here
    # alternatively, we could only support a simplified set of args
    # we don't need much, just just need to know that this is a block
    # being passed in, and we can ignore possible args, forcing the function
    # to rely on scoped variables.
    # we might be able to do this as long as it's not polymorphic
    q.goto(x)

  # next is only called dynamically
  def next_x():
    q.goto("X")

  def next_y():
    q.goto("Y")

  return 0

  """
  we need to resolve next_x, which is in lexical scope here.  But it might not be.  It could follow later
  if the function has no arguments, then it's easy, because monomorphization is trivial
  cps can be polymorphic, just not the continuation
  we need to solve monormorpization of the CPS functions, first before we can do anything more difficult than this
  We don't yet support function identifiers like `next_x`.  They aren't like variables with a clear resolution
  What does `next_x` actually represent?  It could refer to any number of monorphizations of the abstraction referred to
  as `next_x`.  And if we go forward with function defined case-match, we need to support that.
  We could refer to `next_x` as an `abtraction`.  It has no meaning except in the context of a call: either a goto, match, or call.
  So, if we want to goto `cps`, we need to resolve the nested goto first, and this needs to happen through the entire chain of CPS
  calls until we reach a final label, either "X", or "Y".
  We don't need to bake the entire chain, just the ones that depend on the initial parameters, until all calls have been fully baked
  A static chain with no continuations can be monomophized.  When we introduce continuations, we need to have a type on it, so
  we can properly unify it.  There might be some limitations here, but Hindley-Milner should be able to handle it.  We can do more
  complex unifications later with the biunify stuff. 
  So with HM, we pass in the continuation, but it has an unknown type.  We can then bake multiple variants just like we do with
  functions.
  We pass in a continuation of unknown arguments, which needs to be resolved through unification
  Goto can take continuations, or it can take function references, and it's not clear which it is, as long as it's an argument
  So that needs to be unified.  If the argument get's called, then it's a function.  If it gets goto, then it's CPS function.
  And we can fill in the types of the arguments from there.  We have some flexibilty with pythonic arguments, which allow for flexible
  arity.  When we support case-match functions, that will open up other possibilities.

  For `next_x`, we can pass a deferred resolution if we can't find it in the current scope
  we do this for the first argument in goto, but we need something similar for args that get passed.
  We can't just pass in `next_x`, because that doesn't actually evaluate yet, because it's a function.  We can create an abstraction type
  which is similar to what we have for ast_templates.  It corresponds with a polymorphic function, that only gets resolved later
  If we can't find a function, or an identifier, we don't know what it is.  We could just pass in a deferral, and if it's supposed to
  reference a non-existent variable, then we will get a deferral resolution error, which might be fine.  Defining a variable will not 
  resolve the deferral, only defining a function will resolve it.  the deferral should have everything we need to resolve the types
  using unification.  We do what we have already done, which is terminate using the dummy terminator, which will have an unknown type,
  that gets unified.  The dummy terminator will get baked with the function.  The deferrals get resolved by either a label, or a 
  function definition.  But there may be more referrals remaining when we close the scope, due to these continuations.  At the end of
  the scope, monomorphization should be complete.  We have a set of variants that cover all of the calls.  We then just need to finish
  by resolving the remaining continuation referals.

  For the scope finis, we only need 0-arity CPS functions, so we can avoid some of this complexity for now.  We can just enforce
  that all continuations gotos have empty argument sets.  This is all we need to handle the scope exit chains.  But I want to think about
  this, because I think we can support it eventually, as long as we keep in mind what `next_x` represents.  It's not actually a block,
  it's an abstraction, that only gets resolved when used.  So this needs to be unified.

  We can start by getting cps monomorphization working first.  This will keep us on track, while we implement the trivial case for CPS.
  """

  #q.goto(cps, q.resolve_label(next_x))
  q.label("X")
  #q.goto(cps, q.resolve_label(next_y))
  q.label("Y")

  return 0
