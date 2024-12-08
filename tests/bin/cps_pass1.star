q.use("prelude")
def main():
  def cps(x, count):
    q.print(count)
    if count == 0:
      q.goto(x)
    q.goto(cps, x, count - 1)

  def next_w():
    #q.print(x)
    q.goto("D")

  q.goto(cps, next_w, 10)
  q.label("D")

  return 0

