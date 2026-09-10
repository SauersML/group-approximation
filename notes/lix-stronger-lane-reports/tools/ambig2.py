"""Same as ambig.py but counting how many perturbations were actually applied,
and using an exhaustive basis of perturbations rather than random ones."""
import sys
sys.path.insert(0, ".")
from steenrod_descent import *
from itertools import product


def run(p, n, u0, perturb_level=None, zeta=None):
    C = RelSimplexCochains(n)
    (top, ct), = C.delta[u0].items()
    A = {(top,) * p: ct % p}
    W = n * (p - 1)
    lvl = 0
    applied = False
    while W > 0:
        Y = Hop(C, A, p)
        if perturb_level == lvl and zeta:
            dz = Dop(C, zeta, p)
            if dz:
                Y = addv(Y, dz, p)
                applied = True
                assert not addv(Dop(C, Y, p), A, p, -1)
        op = Nop if W % 2 == 0 else TminusOne
        A = op(C, Y, p)
        W -= 1
        lvl += 1
    return pair_with_aw(C, A, n, p), applied


for (n, u0, name) in [(1, (1,), "c_1 on Delta^1"), (2, (1, 2), "c_2 on Delta^2")]:
    for p in (3, 5):
        C = RelSimplexCochains(n)
        base, _ = run(p, n, u0)
        vals = {base}
        napplied = 0
        nlev = n * (p - 1)
        allwords = list(product(C.basis, repeat=p))
        for lvl in range(nlev):
            tgt = n * p - (lvl + 1)          # total degree of Y at this level
            cands = [w for w in allwords if wdeg(C, w) == tgt - 1]
            for w in cands[:400]:
                v, ap = run(p, n, u0, perturb_level=lvl, zeta={w: 1})
                if ap:
                    napplied += 1
                    vals.add(v)
        print(f"{name}, p = {p}: base = {base}, {napplied} non-trivial perturbations, "
              f"values = {sorted(vals)}  -> "
              f"{'WELL DEFINED' if len(vals) == 1 else 'NOT well defined'}", flush=True)
