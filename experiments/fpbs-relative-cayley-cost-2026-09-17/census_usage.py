"""Cross-tabulate the contact census against letter usage.

usage(v) = (number of c^{+-1} letters, number of d^{+-1} letters).
Question: is 'some letter used <= 2 times' equivalent to 'contact or free
factor', i.e. is the no-contact class exactly the k >= 3 class where the
twice-used-letter method dies?"""
import itertools
import sys
from collections import Counter
from census import cyc_reduced, proper_power, canon, analyse, L

maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 8
seen = set()
tab = Counter()
odd = []
for n in range(2, maxlen + 1):
    for tup in itertools.product(L, repeat=n):
        w = ''.join(tup)
        if not cyc_reduced(w) or proper_power(w):
            continue
        nc = sum(1 for x in w if x in 'cC')
        nd = len(w) - nc
        if nc == 0 or nd == 0:
            continue
        cw = canon(w)
        if cw in seen:
            continue
        seen.add(cw)
        ff, hits = analyse(w)
        cls = 'free' if ff else ('contact' if any(h[2] > 0 for h in hits) else 'none')
        k = min(nc, nd)
        band = 'min<=2' if k <= 2 else 'min>=3'
        tab[(band, cls)] += 1
        if band == 'min<=2' and cls == 'none':
            odd.append(w)
        if band == 'min>=3' and cls != 'none':
            odd.append(w)
for key in sorted(tab):
    print(key, tab[key])
print('words breaking the pattern (first 30):', odd[:30])
print('count breaking:', len(odd))
