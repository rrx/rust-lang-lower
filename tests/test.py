def fibonacci(a, b, n):
  if n == 0:
    return a
  elif n == 1:
    return b
  else:
    return fibonacci(b, a + b, n - 1)

def fib(n):
    return fibonacci(0, 1, n)

def f(x):
    return 3 + x

def main():
    y = 2
    return y+1+f(2)+fib(10)
