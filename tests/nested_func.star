q.use("prelude")

def x1():
  if True:
    t = 0

def main() -> int:
  #r = 0
  def f() -> int:
    return 1
  #r = f()
  #r = r - 1
  r = -f()
  #y = 1 + f()
  x = 1 + f() + 1
  return 0
  #return r
