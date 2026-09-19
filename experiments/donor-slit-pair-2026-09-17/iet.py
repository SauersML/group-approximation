from swap import *
import sys
for h in (1, 2):
  for a in (3, 5, 8, 12, 16):
    b, c = cylinder_iet([a, a, a], [2, 1, 0], h)
    r, arg = profile(b, c, min(3*a, 40))
    print("h", h, "a", a, "excess", excess(b, c), "profile>=%.2f at %s" % (r, arg), flush=True)
