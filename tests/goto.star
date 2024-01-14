def main() -> int:
  b.goto("a")
  b.label("a")
  x = 0 if True else (0 if True else 1)
  b.goto("ret")
  b.label("ret")
  return 0

