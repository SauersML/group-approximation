"""Examine one Cayley action: python3 one.py j maxlaw a-perm b-perm (comma lists)."""
import sys
import time
from struct_search import cayley, examine

j = int(sys.argv[1])
ml = int(sys.argv[2])
al = tuple(int(x) for x in sys.argv[3].split(','))
be = tuple(int(x) for x in sys.argv[4].split(','))
PA, PB = cayley(al, be, 10 ** 6)
t0 = time.time()
print('order', len(PA), 'j', j, 'a', al, 'b', be, 'V/Vj/law/deep',
      examine(PA, PB, j, ml)[:4], 'secs', round(time.time() - t0, 1))
