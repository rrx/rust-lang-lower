q.use("prelude")

def main():
  def f(x, *args):
    return x
  y = f(2.1, 1, True)
  z = f(2.2, 1, True)
  q.print(z)
  return f(0, False)
