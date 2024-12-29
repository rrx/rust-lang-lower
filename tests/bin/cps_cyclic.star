def main():
  def f1(x):
    def f1a(x):
      q.goto(x)
    q.goto(f2, x)

  def f2(x):
    z = 0
    def f2a(x):
      z = 1
      q.goto(x)
    q.goto(f2a, x)

  q.goto(f1, A)
  q.label("A")

  return 0
