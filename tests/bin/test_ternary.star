def ident(x) -> int:
  return x

def main():
  #x = 0 if True else (0 if True else 1+1)
  x = 0 if True else (ident(0) if True else ident(1+1))
  return x 
