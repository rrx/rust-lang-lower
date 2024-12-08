def main():
  def cps(x, y, c):
    if c:
      q.goto(x)
    else:
      q.goto(y)

  def next_x():
    q.goto("A")

  def next_y():
    q.goto("B")

  q.goto(cps, next_x, next_y, True)
  q.label("A")
  q.goto(cps, next_y, next_x, True)
  q.label("B")

  return 0
