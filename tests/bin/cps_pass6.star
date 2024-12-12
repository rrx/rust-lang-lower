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

  def U3U2U1(x):
    q.goto(U1, N1)
    q.label("N1")
    q.goto(U2, N2)
    q.label("N2")
    q.goto(U3, x)

  #q.goto_chain(U3, U2, U1, next)
  q.goto(U3U2U1, A)
  q.label("A")
  return 0

