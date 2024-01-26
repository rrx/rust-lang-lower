z = 10

q.use("prelude")

def main() -> int:
  y = 0 + 1
  y = y + 1
  q.print(y)

  # this should mutate the global variable
  q.print(z)
  q.print(z + 1)

  z = z + 1
  q.print(z)
  q.check(z == 11)

  z0 = z
  z = z0
  q.print(z)
  q.check(z == 11)

  # unary integer
  xi = -10

  # local assign, global access
  y = z + xi + 1

  return y - 2

