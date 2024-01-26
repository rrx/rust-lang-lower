q.use("prelude")

def fibonacci_recursive(n: int, a:int, c:int) -> int:
  out = 0
  if n == 0:
    out = a
  elif n == 1:
    out = c
  else:
    out = fibonacci_recursive(n - 1, c, a + c)
  return out


def fib(n: int) -> int:
  return fibonacci_recursive(n, 0, 1)


def main() -> int:
  r1 = fib(10)
  q.check(r1 == 55)
  r1 = fib(19)
  q.check(r1 == 4181)
  return 0

