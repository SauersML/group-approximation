#!/usr/bin/env python3
"""Compare the rank-2 and rank-3 dumps (lines "r1 r2" of canonical states; z is the letter Z/z).
usage: decomp.py s24r2.txt c26r2.txt s24r3.txt c26r3.txt"""
import sys
from collections import Counter
r2a, r2b, r3a, r3b = (set(open(f).read().split('\n')) - {''} for f in sys.argv[1:5])
z = lambda s: 'z' in s.lower()
L = lambda s: len(s) - 1
print('sizes: rank2 S24 %d  rank2 S26 %d  rank3 S24 %d  rank3 S26 %d' % tuple(map(len, (r2a, r2b, r3a, r3b))))
print('rank2 S24 in rank2 S26:', r2a <= r2b, '  rank3 S24 in rank3 S26:', r3a <= r3b)
print('rank2 S24 in rank3 S24:', r2a <= r3a, '  rank2 S26 in rank3 S26:', r2b <= r3b)
for name, s, r in (('rank3 S24', r3a, r2a), ('rank3 S26', r3b, r2b)):
    zf = {t for t in s if not z(t)}
    print('%s: z-free %d, equal to rank2 dump: %s; with z %d' % (name, len(zf), zf == r, len(s) - len(zf)))
    print('   states with z using only two of x, y, z: %d' % sum(1 for t in s if z(t) and len(set(t.lower()) & set('xyz')) < 3))
new = r3b - r3a
print('rank3 S26 minus rank3 S24: %d; z-free %d, equal to rank2 S26 minus rank2 S24: %s' % (
    len(new), sum(1 for t in new if not z(t)), {t for t in new if not z(t)} == r2b - r2a))
print('  z-states by length:', sorted(Counter(L(t) for t in new if z(t)).items()))
print('  z-free by length:  ', sorted(Counter(L(t) for t in new if not z(t)).items()))
