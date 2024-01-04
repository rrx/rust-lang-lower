b.use("prelude")

def main() -> int:
  b.goto("ret")
  b.label("a")
  b.goto("ret")
  b.label("ret")
  return 0

