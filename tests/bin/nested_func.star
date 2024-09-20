q.use("prelude")

def x1():
  if True:
    t = 0
  return 0

# unable to remove types here
def main() -> int:
  r = 0
  zero = 0

  def f1(x):
    return 0
  r = f1(0)

  # these should work
  # f1(0)
  # r2 = f1(1.1)


  def f2(x):
    q.print(x)
    return x+1 

  def f3(x):
    return zero

  r = f2(1)
  r = r - 1
  r = -f2(2)
  y = 1 + f2(3)
  x = 1 + f2(4) + 1
  x1()

  return f3(0)

