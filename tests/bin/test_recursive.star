q.use("prelude")

def fibonacci_recursive(n, a, c):
  out = 0
  if n == 0:
    out = a
  elif n == 1:
    out = c
  else:
    out = fibonacci_recursive(n - 1, c, a + c)
  return out

def fib(n):
  return fibonacci_recursive(n, 0, 1)

def main():
  r1 = fib(1)
  q.check(r1 == 1)
  r1 = fib(10)
  q.check(r1 == 55)
  r1 = fib(19)
  q.check(r1 == 4181)
  return 0

