q.use("prelude")

def main():
  x = 3
  if True:
    def f(next):
      x = x - 1
      q.goto(next)
    q.defer(f)
    q.defer(f)
    q.defer(f)
  return x
