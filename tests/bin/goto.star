# jump to non empty label
def test1():
  q.goto("a")
  q.label("a")
  1
  return 0

# jump to empty label
def test2() -> int:
  q.goto("a")
  q.label("a")
  return 0

# empty label
def test3() -> int:
  q.label("a")
  return 0

# non-empty label
def test4() -> int:
  q.label("a")
  1
  return 0

def main() -> int:
  q.goto("a")
  q.label("a")
  x = 0 if True else (0 if True else 1+1)
  x = 0
  q.goto("ret2")
  q.label("ret2")
  return 0

