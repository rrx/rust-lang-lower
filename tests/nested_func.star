q.use("prelude")

def x1():
  if True:
    t = 0

def main() -> int:
  r = 0
  def f(x: int) -> int:
    q.print(x)
    return x+1 
  r = f(1)
  r = r - 1
  r = -f(2)
  y = 1 + f(3)
  x = 1 + f(4) + 1
  #return 0
  return f(-1)
