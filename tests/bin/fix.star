q.use("prelude")

def test2(n):
  out = 0
  if True:
    out = n
    q.check(out == n)
    x = n
  return 0

def main():
  test2(0)
  return 0

