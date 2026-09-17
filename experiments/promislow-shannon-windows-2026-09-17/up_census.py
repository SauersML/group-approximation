#!/usr/bin/env python3
"""Tabulate the census outputs of ../shannon-window-certificates-2026-09-17 by (fake?, UP?), where the pair (F, E)
is UP if some product f e in FE has a unique representation.  Tests whether unique products govern the fakes.
usage: up_census.py
"""
import re, ast, collections, os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shannon-window-certificates-2026-09-17')
files = {'cyclic_z3.txt': 3, 'cyclic_z4.txt': 4, 'cyclic_z5.txt': 5, 'rs_z5.txt': 5, 'rs_z7.txt': 7, 'rs_zz3.txt': 'zz3'}
pat = re.compile(r'E=\{(.*?)\} F=\{(.*?)\}.*LP=([\d.]+)')
for fn, n in files.items():
    tab = collections.Counter()
    ex = []
    for line in open(os.path.join(D, fn)):
        m = pat.search(line)
        if not m:
            continue
        E = list(dict.fromkeys(ast.literal_eval('[' + m.group(1) + ']')))
        F = list(dict.fromkeys(ast.literal_eval('[' + m.group(2) + ']')))
        lp = float(m.group(3))
        c = collections.Counter()
        for f in F:
            for e in E:
                if n == 'zz3':
                    c[(f[0] + e[0], (f[1] + e[1]) % 3)] += 1
                else:
                    c[(f + e) % n] += 1
        up = any(v == 1 for v in c.values())
        fake = lp < 1 - 1e-6
        tab[(fake, up)] += 1
        if fake and up:
            ex.append(line.strip())
    print(fn, '(fake, UP) counts:', dict(tab))
    for e in ex[:5]:
        print('   UP-but-fake:', e)
