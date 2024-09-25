load("prelude", "q")
z = 0
def main():
  q.check(z == 0)
  z = z + 1
  q.check(z == 1)
  return z - 1
