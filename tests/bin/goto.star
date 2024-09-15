# jump to non empty label
def test1():
  q.goto("a")
  q.label("a")
  1

# jump to empty label
def test2():
  q.goto("b")
  q.label("b")

# empty label
def test3():
  q.label("c")

# non-empty label
def test4():
  q.label("d")
  1

# function with no return type
def f():
  1

def main():
  q.goto("e")
  q.label("e")
  x = 0 if True else (0 if True else 1+1)
  x = 0
  test1()
  test2()
  test3()
  test4()
  f()
  q.goto("ret2")
  q.label("ret2")
  return 0

