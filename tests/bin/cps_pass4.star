q.use("prelude")
def main():
  count = 0
  def cps(x, y, c):
    z = x
    if c:
      q.print(10)
      q.goto(x)
    else:
      q.print(22)
      q.goto(cps, next_y, next_x, True)

  def next_x():
    q.goto("A")

  def next_y():
    q.goto("B")

  q.goto(cps, next_x, next_y, False)
  q.label("A")
  q.check(False)
  q.label("B")
  count = count + 1
  q.check(count == 1)
  return 0
