q.use("prelude")
def main():
  def f(x):
    q.print(x)
    if x > 0:
      q.goto("A")
    else:
      q.goto("B")

  q.goto(f, 1)
  q.label("A")

  # TODO: monomorphization isn't supported yet
  # we need to generate the variants and jump appropriately
  #q.goto(f, -1.1)
  q.label("B")
  return 0
