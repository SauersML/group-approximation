"""Re-examine the MIX cases (X < Z < Y) printed by dichotomy.py.

For each case recompute X, J, Y, Z and the free-factor/SHN bound
    rk(Y:X) <= (rk Y - rk Z) + rk(Z:X)
with rk(Z:X) <= 1 certified exactly by relrank_le1 (else reported as '>=2?').
Also report whether X is a free factor of Z (d(Z:X) = 0 test for rk(Z:X) = 1:
rk Z = rk X + 1).

usage: mix_check.py file host k
"""
import ast
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dichotomy import classify  # noqa: E402
from census import (graph_of, compact, relrank_le1, fold, canon, rank,  # noqa
                    fi_subgroup, phij)


def host_graph(kind, ws):
    if kind in ('L1overL2', 'L2overL3'):
        j = 1 if kind == 'L1overL2' else 2
        return compact(*graph_of(ws)), ['a', phij('b', j + 1)]
    return compact(*graph_of(ws)), ws


def main(path, kind, k):
    pat = re.compile(r"CASE MIX rr=\S+ host=(\[.*?\]) X=(\(.*?\)) prs=(\[.*?\]) ")
    tally = {}
    for line in open(path):
        mt = pat.search(line)
        if not mt:
            continue
        ws = ast.literal_eval(mt.group(1))
        desc = ast.literal_eval(mt.group(2))
        prs = [tuple(p) for p in ast.literal_eval(mt.group(3))]
        (nB, EB), Cws = host_graph(kind, ws)
        if desc[0] == 'sub':
            nx, Ex = compact(*graph_of(desc[1]))
        else:
            nx, Ex = fi_subgroup(Cws, desc[2])
        cls, rks, (ny, Ey, cy), (mz, Fz) = classify(nx, Ex, nB, EB, prs)
        assert cls == 'MIX'
        rX, rJ, rY, rZ = rks
        nz, Ez = compact(mz, Fz)
        zx = relrank_le1(nx, Ex, nz, Ez)
        rzx = 1 if zx in ('arc', 'pair') else None
        bound = (rY - rZ + rzx) if rzx else None
        key = (zx, rY - rZ, bound is not None and bound <= k)
        tally[key] = tally.get(key, 0) + 1
        print('MIX rk X,J,Y,Z=%s  Z over X: %s  rkY-rkZ=%d  bound=%s'
              % (rks, zx, rY - rZ, bound))
    print('tally (Z:X certificate, rkY-rkZ, bound<=k):', tally)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
