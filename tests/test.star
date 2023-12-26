# just a static var
z = 1

b.use("prelude")

def main() -> int:
  out = z
  if True:
    out = 0
    return out

  return out
