q.use("prelude")

def main() -> int:
  z = 10
  q.loop("loop1")
  if z == 0:
    q.loop_break
  else:
    q.print(z)
    z = z - 1
    q.loop_continue
  q.end

  y = 10
  q.loop
  if y == 0:
    q.loop_break
  y = y - 1
  q.end

  return y + z

