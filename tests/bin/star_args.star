q.use("prelude")

def keyword_arg(x, *args, asdf=1):
  q.print(asdf)
  return asdf

def positional(x, *args, asdf=1):
  q.print(x)
  return x

def main():
  q.check(positional(10) == 10)
  # this doesn't work yet, because we only make one version of a def currently
  # the second type signature does not unify
  #q.check(keyword_arg(10, asdf=11) == 11)
  q.check(keyword_arg(10, 11, 12, True, False, asdf=11) == 11)
  return 0
