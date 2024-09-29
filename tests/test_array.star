q.use("prelude")

#a = [1,2,3]
#d = {1: 2}
#a = q.array(int, 1,2)

def main() -> int:
  x = 0
  t = (0,x,0)
  y = t[0]
  q.check(y == 0)
  q.print(t[0])
  q.print(t[1])
  q.print(t[2])
  q.check(t[2] == 0)
  return t[2]

