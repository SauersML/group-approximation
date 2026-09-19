"""Keep the Garside-genuine records, one per (a1, b1, a2) (the x-arcs, hence the ejection pattern, do not see b3).
Optional word filter: only records whose zero-winding alpha involves p1.  Run: python3 gfilter.py in out [p1]"""
import sys, json
from collections import Counter
from ejection import elt, genuine

seen, st = set(), Counter()
fo = open(sys.argv[2], 'w')
for line in open(sys.argv[1]):
    r = json.loads(line)
    if len(sys.argv) > 3 and not any(len(r[k].split()) == 4 and 'p1' in r[k] for k in ('a1', 'a2')):
        continue
    k = (r['a1'], r['b1'], r['a2'])
    if k in seen:
        continue
    if genuine(*(elt(r[x]) for x in ('a1', 'b1', 'a2', 'b3'))):
        seen.add(k); fo.write(line); st['genuine'] += 1
    else:
        st['not genuine'] += 1
print(dict(st))
