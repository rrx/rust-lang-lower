# just a static var
z = 1

b.use("prelude")

def main() -> int:
  out = z
  if True:
    out = 0
    #b.check(out > 0)
    return out

  b.check(out > 0)
  return out
