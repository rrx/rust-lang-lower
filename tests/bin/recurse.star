def f(x):
  q.print(x)
  if x == 0:
    return 0
  return f(x-1)

def main():
  return f(10)

