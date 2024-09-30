q.use("prelude")

def main() -> int:
  t = (2,1,0)
  q.check((2,1,0)[0] == 2)
  q.check((2,1,0)[1] == 1)
  q.check((2,1,0)[2] == 0)
  x = 0
  t = (0,x,0)
  y = t[0]
  q.check(y == 0)
  q.print(t[0])
  q.print(t[1])
  q.print(t[2])
  q.check(t[2] == 0)
  return t[2]

