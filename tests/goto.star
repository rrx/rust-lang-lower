def main() -> int:
  q.goto("a")
  q.label("a")
  x = 0 if True else (0 if True else 1)
  q.goto("ret")
  q.label("ret")
  return 0

