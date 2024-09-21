def main():
  def f(x, *args):
    return x
  y = f(2.1, 1, True)
  return f(0, False)
