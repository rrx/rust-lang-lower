
def main():
  def f(x, *args):
    return x
  z = f(1, False)
  y = f(1.1, 1, True)
  return 0
