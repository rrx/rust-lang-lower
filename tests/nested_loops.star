def main() -> int:
  q.loop("loop1")
  q.loop("loop2")
  q.loop("loop3")

  q.loop("loop4")
  q.loop_break("loop2") 
  q.end

  q.end

  # loop 2
  q.loop_break
  q.end
  q.loop_break
  q.end
  return 0
  
