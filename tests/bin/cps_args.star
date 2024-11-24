q.use("prelude")

def main():
  def label_d(x, *args):
    q.goto(label_e, x, *args)

  q.goto(label_d, 1, 1, True)

  def label_e(x, *args):
    q.print(x)
    q.goto("final")

  q.label("final")

  return 0
