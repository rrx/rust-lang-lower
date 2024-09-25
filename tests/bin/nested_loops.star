def main():
  q.loop("loop1")
  q.loop("loop2")
  q.loop("loop3")

  q.loop("loop4")
  q.loop_break("loop2") 
  q.end

  q.end

  # loop 2
  q.loop_break
  return 1
  q.end
  q.loop_break
  1
  q.end
  return 0
