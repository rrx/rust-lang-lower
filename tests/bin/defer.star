q.use("prelude")

def main():
  x = 1
  if True:
    def f():
      x = 0
    q.defer(f)
  return 0 
