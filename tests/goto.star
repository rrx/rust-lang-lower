b.use("prelude")

def main() -> int:
  b.goto("a")
  b.label("a")
  b.goto("ret")
  b.label("ret")
  return 0

