# Retest screen survivors (JSON lines with R0, R1) against larger perfect groups.
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from screen import load, homs
src, names = sys.argv[1], sys.argv[2].split(',')
grps = {nm: load(nm) for nm in names}
for line in open(src):
    v = json.loads(line); R = (v['R0'], v['R1']); res = []
    for nm in names:
        c, wit = homs(R, grps[nm]); res.append('%s:%d' % (nm, c))
        if c: break
    print(v['mode'], v['seed'], v['var'], v['sgn'], len(R[0]), len(R[1]), ' '.join(res), flush=True)
