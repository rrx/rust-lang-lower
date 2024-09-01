def test1():
  q.goto("a")
  q.label("a")
  1

def test2():
  q.goto("a")
  q.label("a")

def main() -> int:
  q.goto("a")
  q.label("a")
  x = 0 if True else (0 if True else 1+1)
  q.goto("ret2")
  q.label("ret2")
  return 0

