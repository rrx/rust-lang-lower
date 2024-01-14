def fibonacci_recursive(n: int, a:int, c:int) -> int:
  out = 0
  if n == 0:
    out = a
  elif n == 1:
    out = c
  else:
    out = fibonacci_recursive(n - 1, c, a + c)
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
  r = fibonacci_recursive(2,0,1)
  r = fibonacci(0,1,2)
  return 0

