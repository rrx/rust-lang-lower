z = 6
zf = 1.2

b.use("prelude")

def fibonacci_recursive(n: int, a:int, c:int) -> int:
  b.print(n)
  b.print(a)
  b.print(c)
  out = 0
  if n == 0:
    out = a
  elif n == 1:
    out = c
  else:
    out = fibonacci_recursive(n - 1, c, a + c)
  b.print(out)
  return out

def x1(x: int) -> int:
  return 2 + x

def xf(x: float) -> float:
  return 2.2 + x


def fibonacci(a:int, c:int, n:int)->int:
  out = 0
  if n == 0:
    out = a
  elif n == 1:
    out = c
  else:
    out = fibonacci(c, a + c, n - 1)
  return out

def cond(n: int) -> int:
  out = 0
  out = out - 1
  if n == 0:
    out = 1
  elif n == 1:
    out = 2
  else:
    out = 3
  return out

def test()->int:
  out = 0
  if out == 0:
    out = 1
  #b.check(out == 1)
  return 0

def main() -> int:
  # test reference of global variable
  # test calling function with zero arguments
  b.print(1.5)
  zz = 6.4
  zz = zf + 1.5 + zz
  zz = zz + 1.0
  z = z + 1
  #b.print(fibonacci_recursive(2,0,1))
  #b.print(fibonacci(0,1,2))
  b.print(cond(0))
  b.print(cond(1))
  b.print(cond(2))
  test()
  return z - 9 + x1(0)
