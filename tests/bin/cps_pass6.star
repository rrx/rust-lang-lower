q.use("prelude")
def main():
  def U3(x):
    q.print(2)
    q.goto(x)
  def U2(x):
    q.print(1)
    q.goto(x)
  def U1(x):
    q.print(0)
    q.goto(x)

  def next():
    q.goto("A")

  #q.goto_chain(U3, U2, U1, next)
  q.goto(U3, A)
  q.label("A")
  return 0

