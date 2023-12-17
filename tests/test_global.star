z = 6

b.use("prelude")

def x1(x: int) -> int:
  return 2 + x

def test()->int:
  out = 0
  if out == 0:
    out = 1
  #b.check(out == 1)
  return 0

def main() -> int:
  # test reference of global variable
  # test calling function with zero arguments

  # this should mutate the global variable
  #z = z + 1
  test()

  # test function with 1 int arg
  return z - 9 + x1(0) + 1
