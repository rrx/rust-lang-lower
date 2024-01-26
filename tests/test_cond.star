q.use("prelude")

def cond(n: int) -> int:
  out = 0
  out = out - 1
  if n == 0:
    out = 1
  elif n == 1:
    out = 2
  else:
    out = 3
  return out

def main() -> int:
  q.print(cond(0))
  q.print(cond(1))
  q.print(cond(2))
  return 0
