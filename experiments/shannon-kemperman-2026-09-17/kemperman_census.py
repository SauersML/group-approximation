#!/usr/bin/env python3
"""Compare minimal-window Shannon LP fakes with sumset saturation |FE| < |E| + |F| - 1.

Reads the cyclic census outputs of the earlier lanes and tabulates (n, fake?, saturation class).
Run from the repository root.
"""
import re, glob, collections

files = (glob.glob('experiments/shannon-window-certificates-2026-09-17/cyclic_z*.txt')
         + glob.glob('experiments/shannon-window-certificates-2026-09-17/rs_z[57].txt')
         + glob.glob('experiments/promislow-shannon-windows-2026-09-17/cps_z*.txt'))
cnt = collections.Counter()
for fn in sorted(files):
    for line in open(fn):
        m = re.search(r'[zZ]/?(\d+) E=\{([^}]*)\} F=\{([^}]*)\}.*LP=([\d.]+)', line)
        if not m:
            continue
        n = int(m.group(1))
        E = [int(a) for a in m.group(2).split(',')]
        F = [int(a) for a in m.group(3).split(',')]
        lp = float(m.group(4))
        FE = {(f + e) % n for f in F for e in E}
        k = len(E) + len(F) - 1
        cls = 'sat' if len(FE) < k else ('eq' if len(FE) == k else 'big')
        cnt[(n, lp < 0.9999, cls)] += 1
        if lp < 0.9999 and cls != 'sat':
            print('fake without saturation:', fn.split('/')[-1], line.strip(), '|FE| =', len(FE))
for key in sorted(cnt):
    print(key, cnt[key])
