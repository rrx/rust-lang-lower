q.use("prelude")

def x1():
  if True:
    t = 0

def main() -> int:
  r = 0
  zero = 0

  def f1(x: int):
    return
  f1(0)

  def f2(x: int) -> int:
    q.print(x)
    return x+1 

  def f3(x: int) -> int:
    return zero

  r = f2(1)
  r = r - 1
  r = -f2(2)
  y = 1 + f2(3)
  x = 1 + f2(4) + 1

  return f3(0)

