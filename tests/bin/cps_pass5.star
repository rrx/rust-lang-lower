q.use("prelude")
def main():
  def cps(x):
    q.goto(x)

  q.goto(cps, A)
  q.label("A")
  q.goto(cps, B)
  q.label("B")
  return 0
