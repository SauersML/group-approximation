#!/usr/bin/env python3
"""Calibration: is the thickenable target reached earlier than the basis target?
Runs acthick.search on AK(2) and Miller-Schupp presentations
MS(n,w) = <x,y | x^-1 y^n x = y^(n+1), x = w>  (w of x-exponent sum 0),
with target 'basis' (total length 2) and target 'thick' (Neuwirth-thickenable),
same move set and caps, and prints the number of states generated before a hit.
Usage: calib_ms.py [slack] [maxstates]
"""
import sys, time
import acthick as A

slack = int(sys.argv[1]) if len(sys.argv) > 1 else 2
ms = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
cases = [('AK2', 'xyxYXY', 'xxYYY')]
for n in (1, 2, 3):
    r1 = 'X' + 'y' * n + 'x' + 'Y' * (n + 1)
    for w in ('y', 'yy', 'xyX', 'YxyX', 'xyyX', 'yxYX', 'xYYX', 'yxyX', 'xyXy'):
        cases.append(('MS(%d,%s)' % (n, w), r1, A.cred('X' + w)))
for name, r1, r2 in cases:
    L = max(len(r1), len(r2)) + slack
    row = [name, r1, r2, 'cap%d' % L]
    for tgt in ('basis', 'thick'):
        t0 = time.time()
        st, path, n = A.search(r1, r2, L, ms, aut=True, target=tgt, per=True)
        row.append('%s:%s/%d/%s' % (tgt, st, n, (len(path) - 1) if path else '-'))
    print(' '.join(row)); sys.stdout.flush()
