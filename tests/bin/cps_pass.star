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
  #q.goto(cps, q.resolve_label(next_x))
  q.label("X")
  #q.goto(cps, q.resolve_label(next_y))
  q.label("Y")

  return 0
