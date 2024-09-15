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
  1
  q.label("d")
  1

# non-empty label
def test5():
  1
  1
  q.label("e")

# function with no return type
def f():
  1
  1

def ident(x) -> int:
  return x

def main():
  q.goto("f")
  q.label("f")
  x = ident(0)
  test1()
  test2()
  test3()
  test4()
  test5()
  f()
  q.goto("ret2")
  q.label("ret2")
  return 0

