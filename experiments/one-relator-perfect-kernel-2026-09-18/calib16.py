"""Calibration of linfree.py on the landed length-16 Linton run (lg_words16.out).
For each VERDICT line with a rank-2 (m = 2) Magnus piece, recompute the Magnus rewriting exactly as
lintongraph.py 'words' does, and certify through the Whitehead-tracked basis of linfree.py.
Visibly free pieces (landed PASS) must again PASS.  Pieces the landed run called NONFREE are
Whitehead-tested; a primitive one is certified through the tracked basis.
Usage: calib16.py lg_words16.out"""
import sys, math
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/or-unpeelable-census-scripts-2026-09-12')
import census as C
import linfree as LF

code = {'a': 1, 'A': -1, 't': 2, 'T': -2}
for line in open(sys.argv[1]):
    f = line.split()
    if not f or f[0] != 'VERDICT':
        continue
    landed = f[-1]
    wtxt = f[3] if f[1] == 'WORDS' and f[2].startswith('phi') else (f[2] if f[1] == 'WORDS' else None)
    if f[1] == 'WORDS' and f[2].startswith('phi'):
        x, yy = map(int, f[2][4:].split(','))
        phis = [(x, yy)]
    else:
        wtxt = f[2]
        w = [code[ch] for ch in wtxt]
        p, q = C.expsums(w)
        phis = [(q // math.gcd(p, q), -p // math.gcd(p, q))] if (p, q) != (0, 0) else C.small_phis()
    w = [code[ch] for ch in wtxt]
    for x, yy in phis:
        seq = C.magnus(C.adapt(list(w), x, yy))
        if seq is None:
            continue
        cs = list(C.canon(seq))
        n = max(h for h, _ in cs)
        if n != 2:
            print('CALIB %s n=%d skip' % (wtxt, n))
            continue
        W = []
        for h, e in cs:
            W += [h + 1 if e > 0 else -(h + 1)] * abs(e)
        v, rest = LF.run(W)
        print('CALIB %s landed=%s tracked=%s' % (wtxt, landed, v), flush=True)
        break
print('SENTINEL_DONE')
