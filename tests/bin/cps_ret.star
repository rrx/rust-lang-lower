q.use("prelude")
def main():
  def f1():
    q.goto("A")
  def f2():
    q.goto("A")

  def f(c):
    if c:
      return f2
    else:
      return f1

  a = f(True)
  q.print(a)

  c = f(True)
  q.print(c)
  #a()
  q.label("A")
  return 0
