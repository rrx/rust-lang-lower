q.use("prelude")

def main():
  count = 0

  # CPS function that never returns
  def unit(x):
    # verify that the function scope here is able to access highler level scopes
    # by jumping to B
    # deferred goto
    q.print(x)
    count = count + 1
    q.goto(label_c, x+1)
    # nothing happens here
    1

  def label_d(x):
    q.print(x)
    # deferred goto
    count = count + 1
    q.goto(label_e, x+1)

  def label_c(x):
    q.print(x)
    q.check(x == 2)
    count = count + 1
    q.goto("B")

  1

  # this is how we call a CPS function, it's just a jump to the identifier
  # and we bake a CPS function
  q.goto(unit, 1)

  # nothing happens here
  1

  # the CPS function lands here
  q.label("B")

  1
  # we can only goto a cps function that has already been declared in scope
  # it should be possible to goto a cps function that is declared in the scope
  # but further down
  q.goto(label_d, 1)

  1

  def label_e(x):
    q.print(x)
    q.check(x == 2)
    count = count + 1
    q.goto("final")
    1

  1

  q.label("final")
  1
  q.goto("last")
  1
  q.label("last")
  1
  q.check(count == 4)
  1
  return 0
