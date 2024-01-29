q.use("prelude")

def main() -> int:
  r = 0
  def f() -> int:
    return 1
  r = f()
  r = r - 1
  return r
