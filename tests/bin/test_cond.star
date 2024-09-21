q.use("prelude")

def cond(n):
  out = 0
  out = out - 1
  if n == 0:
    out = 1
  elif n == 1:
    out = 2
  else:
    out = 3
  return out

def main():
  q.check(1 == cond(0))
  q.check(2 == cond(1))
  q.check(3 == cond(2))
  return 0
