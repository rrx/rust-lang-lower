# just a static var
z = 1

q.use("prelude")

def main() -> int:
  out = z
  out2 = z

  if False:
    out = out + 1
    q.check(out == 2)
    q.print(out)

  q.check(out == 1)

  if True:
    out2 = 0
    q.check(out2 == 0)
    q.print(out2)

    out = out - 1
    q.check(out == 0)
    q.print(out)
    return out

  q.check(out > 0)
  q.print(out)
  return out
