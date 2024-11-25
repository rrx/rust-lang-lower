q.use("prelude")
def main():
  def f(x, y):
    q.print(x)
    if x > y:
      q.goto("A")
    else:
      q.goto("B")

  q.goto(f, 1, 0)
  q.label("A")

  q.goto(f, -1.1, 0.0)
  q.label("B")

  return 0
