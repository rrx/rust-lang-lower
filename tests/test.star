# just a static var
z = 1

q.use("prelude")

def main() -> int:
  out = z
  if True:
    out = 0
    #q.check(out > 0)
    return out

  q.check(out > 0)
  return out
