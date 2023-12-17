zf = 1.2

b.use("prelude")

def xf(x: float) -> float:
  return 2.2 + x + zf

def main() -> int:
  zz = 6.4
  zz = zf + 1.5 + zz
  zz = zz + 1.0

  y =(xf(zz))
  b.print(y)


