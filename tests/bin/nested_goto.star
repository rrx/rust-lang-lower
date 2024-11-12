# nested label
def main():
  if True:
    q.goto("b")
    if True:
      q.goto("c")
  q.label("b")
  q.label("c")
  return 0

