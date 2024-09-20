q.use("prelude")

def main():
  z = 10
  q.loop("loop1")
  if z == 0:
    q.loop_break
  else:
    q.print(z)
    z = z - 1
    q.loop_continue
  q.end
  q.check(z == 0)

  y = 10
  q.loop
  if y == 0:
    q.loop_break
  y = y - 1
  q.loop_continue
  q.end
  q.check(y == 0)

  a = 0
  q.loop
  a = a + 1
  q.print(a)
  if a > 1000:
    q.loop_break

  q.loop_continue
  q.end

  q.loop
  q.loop_break
  q.end

  return y + z

