q.use("prelude")

def main():
  def f(asdf):
    q.print(asdf)
    return asdf

  x = f(1)
  y = f(1)

  q.print(x)
  q.print(y)

  q.check(x == 1)
  q.check(y == 1)

  return 0
