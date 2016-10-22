#!/usr/bin/env python
def parse(line):
  ints = [int(s) for s in line.split()]
  i0 = ints.index(0)
  return ints[0], ints[1:i0], ints[i0+1:-1]
def verify(file):
  cs = {}
  for id, c, ids in (parse(line) for line in file):
    if id:
      if ids:
        d = set(c)
        for i in ids:
          e = set(cs[i])-d
          if e:
            d.add(-e.pop())
            assert not e
          else:
            cs[id] = c
            if not c:  return "VERIFIED"
      else:  cs[id] = c
    else:
      for id in ids:  del cs[id]
  return "NOT VERIFIED"
if __name__ == "__main__":
  import sys
  print(verify(open(sys.argv[1])))
