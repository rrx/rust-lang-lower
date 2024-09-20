q.use("prelude")

# unable to remove types on recursive function
def fibonacci_recursive(n: int, a:int, c:int) -> int:
  out = 0
  if n == 0:
    return a
  elif n == 1:
    return c
  else:
    return fibonacci_recursive(n - 1, c, a + c)

def fib(n):
  x = fibonacci_recursive(n, 0, 1)
  return x

def main():
  r1 = fib(10)
  q.check(r1 == 55)
  r1 = fib(19)
  q.check(r1 == 4181)
  return 0


