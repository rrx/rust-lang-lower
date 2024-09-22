q.use("prelude")

def test1():
  return 1

# the second implementation takes precedence currently
# we want this to compile at least for now, though 
# we may want to produce an error later
def test1():
  return 0

def main() -> int:
  x = test1()
  q.print(x)
  q.check(x == 0)
  return 0
