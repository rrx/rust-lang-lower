q.use("prelude")

def main():
  def f(x, *args):
    return x

  # we should only bake 2 versions
  # an int version and a float version
  # we don't currently have a way of knowing how many versions there are
  y = f(2.1, 1, True)
  z = f(2.2, 1, True)
  z = f(2.3, 1, True)
  z = f(2.4, 1, True)
  q.print(z)
  return f(0, False)
