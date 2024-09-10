q.use("prelude")

def fibonacci_recursive2(n: int, a:int, c:int) -> int:
  out = 0
  if n == 0:
    return a
  elif n == 1:
    return c
  else:
    return fibonacci_recursive2(n - 1, c, a + c)

def fib(n: int) -> int:
  return fibonacci_recursive2(n, 0, 1)

def main() -> int:
  r1 = fib(10)
  q.check(r1 == 55)
  r1 = fib(19)
  q.check(r1 == 4181)
  return 0


