q.use("prelude")

def main():
  def f2(asdf):
    q.print(asdf)
    return asdf
  def f1(asdf):
    q.print(asdf)
    return asdf

  x = f2(1)
  y = f2(1)

  q.print(x)
  q.print(y)

  q.check(x == 1)
  q.check(y == 1)

  return 0
