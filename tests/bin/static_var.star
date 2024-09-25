x = 3
def f():
  q.check(x == 3)
  q.static("x", 1)
  x = x + 1
  return x

def main():
  q.check(x == 3)
  q.check(f() == 2)
  q.check(f() == 3)
  q.check(x == 3)
  q.static("x", 0)
  q.check(x == 0)
  return x

