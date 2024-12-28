q.use("prelude")

def main():
  x = 1
  if True:
    def deferred():
      x = 0
    q.defer(deferred)
  return 0 
