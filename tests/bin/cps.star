q.use("prelude")

def main():
  def label_c(x):
    q.print(x)
    q.goto("B")

  # CPS function that never returns
  def unit(x):
    # verify that the function scope here is able to access highler level scopes
    # by jumping to B
    q.goto(label_c, x)
    # nothing happens here
    1

  # this is how we call a CPS function, it's just a jump to the identifier
  # and we bake a CPS function
  q.goto(unit, 1)

  # nothing happens here
  1


  # the CPS function lands here
  q.label("B")
  return 0
