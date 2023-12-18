z = 10

b.use("prelude")

def main() -> int:
  y = 0 + 1
  y = y + 1
  b.print(y)

  # this should mutate the global variable
  b.print(z)
  #b.print(z + 1)
  z = z + 1
  b.print(z)
  b.check(z == 11)

  # unary integer
  #xi = -10

  # local assign, global access
  #y = z + xi + 1
  #return y - 2
  return 0

