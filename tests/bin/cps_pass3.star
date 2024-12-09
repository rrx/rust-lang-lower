q.use("prelude")
def main():
  def cps(x, y, c):
    z = x
    q.print(20)
    q.print(c)
    if c:
      q.print(10)
      z = y
    q.print(z)
    q.print(x)
    q.print(y)
    q.check(x != y)
    q.goto(z)

  def next_x():
    q.goto("A")

  def next_y():
    q.goto("B")

  count = 1
  q.goto(cps, next_x, next_y, True)
  q.label("A")
  count = count - 1
  q.goto(cps, next_x, next_y, False)
  q.label("B")
  count = count - 1

  return count

