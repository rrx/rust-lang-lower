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

def fibonacci(a:int, c:int, n:int)->int:
  out = 0
  if n == 0:
    out = a
  elif n == 1:
    out = c
  else:
    out = fibonacci(c, a + c, n - 1)
  return out

def main() -> int:
  b.print(fibonacci_recursive(2,0,1))
  b.print(fibonacci(0,1,2))

