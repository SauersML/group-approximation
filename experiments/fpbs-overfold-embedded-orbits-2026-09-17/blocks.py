"""Block decomposition of deep_j and exact block tests.

Fold closures never leave the components they touch, so for an optimal seed
set P, group the L_j-orbits into blocks linked by cross-orbit seeds of P; the
seeds inside a block W collapse the kernel over W by themselves.  Hence

    deep_j(Q) = min over partitions of the L_j-orbits into blocks W of
                sum_W deepc(W),

where deepc(W) is the least number of seeds with both ends over W whose
closure collapses ker(m) over W.  So deep < law iff some block W has
deepc(W) < law(W) = sum_{O in W} law_O.  This script tests all blocks of
b orbits (b = 2, 3, ...) exactly with deep.c on the restricted instance.

Usage: python3 blocks.py j b timeout_s PA PB     (PA, PB comma lists)
"""
import os
import re
import subprocess
import sys
import tempfile
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import depth_graphs, closure  # noqa: E402

DEEP = os.environ.get('DEEP_BIN', os.path.join(HERE, 'deep'))
KEYS = [('a', 1), ('a', -1), ('b', 1), ('b', -1)]


def comps(nbs, V):
    lab = [-1] * V
    k = 0
    for s in range(V):
        if lab[s] >= 0:
            continue
        lab[s] = k
        st = [s]
        while st:
            v = st.pop()
            for u in nbs[v].values():
                if lab[u] < 0:
                    lab[u] = k
                    st.append(u)
        k += 1
    return k, lab


def canon(cls):
    first = {}
    return tuple(first.setdefault(c, len(first)) for c in cls)


def setup(PA, PB, j):
    Gj, G, m = depth_graphs(PA, PB, j)
    kj, labj = comps(Gj.nb, Gj.V)          # L_j-orbit of each Gamma_j vertex
    orb = [labj[m[v]] for v in range(G.V)]  # L_j-orbit under each Gamma_{j+1} vertex
    return Gj, G, m, kj, orb


def instance(G, m, orb, W):
    Wset = set(W)
    verts = [v for v in range(G.V) if orb[v] in Wset]
    idx = {v: i for i, v in enumerate(verts)}
    fib = {}
    for v in verts:
        fib.setdefault(G.over[v], []).append(v)
    reps = {}
    law = set()
    for vs in fib.values():
        for x in range(len(vs)):
            for y in range(x + 1, len(vs)):
                u, v = vs[x], vs[y]
                c = canon([cl for cl in closure(G, [(u, v)])])
                lawful = m[u] == m[v]
                if c not in reps or (lawful and c not in law):
                    reps[c] = (u, v, lawful)
                    if lawful:
                        law.add(c)
    mm = {}
    out = [f"{len(verts)} {len(verts)}"]
    for v in verts:
        out.append(' '.join(str(idx[G.nb[v][k]]) if k in G.nb[v] else '-1' for k in KEYS))
    out.append(' '.join(str(mm.setdefault(m[v], len(mm))) for v in verts))
    out.append(' '.join(str(G.over[v]) for v in verts))
    out.append(str(len(reps)))
    ncross = 0
    for (u, v, lw) in reps.values():
        out.append(f"{idx[u]} {idx[v]} {1 if lw else 0}")
        ncross += (not lw) and orb[u] != orb[v]
    out.append('0')
    return '\n'.join(out), len(verts), len(reps), ncross


def run(inst, level, lawonly, timeout):
    with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False) as f:
        f.write(inst)
        path = f.name
    args = [DEEP, path, str(level)] + (['law'] if lawonly else [])
    try:
        out = subprocess.run(args, capture_output=True, text=True, timeout=timeout).stdout
        done = True
    except subprocess.TimeoutExpired as ex:
        out = ex.stdout.decode() if isinstance(ex.stdout, bytes) else (ex.stdout or '')
        done = False
    os.unlink(path)
    mt = re.search(r'level (\d+) GOAL', out)
    if mt:
        return int(mt.group(1)), True
    if 'level 0 goal' in out:
        return 0, True
    comp = [int(x) for x in re.findall(r'level (\d+): no goal', out)]
    return None, (max(comp) if comp else 0) if not done else 'complete'


def test_blocks(PA, PB, j, b, timeout, log=print):
    Gj, G, m, kj, orb = setup(PA, PB, j)
    lawO = {}
    for O in range(kj):
        inst, _, _, _ = instance(G, m, orb, [O])
        lawO[O], _ = run(inst, 40, True, timeout)
    res = []
    for W in combinations(range(kj), b):
        inst, nv, ns, ncross = instance(G, m, orb, W)
        if nv > 256:
            res.append((W, 'skip V>256'))
            continue
        lw = sum(lawO[O] for O in W)
        if ncross == 0:
            res.append((W, lw, 'no cross seeds'))
            continue
        d, st = run(inst, lw - 1, False, timeout)
        if d is not None:
            verdict = 'COUNTEREXAMPLE' if d < lw else 'ok'
        elif st == 'complete':
            verdict = 'deepc=law'
        else:
            verdict = f'deepc>={st + 1} (timeout)'
        res.append((W, lw, ns, ncross, verdict))
        log('  block', W, 'V', nv, 'law', lw, 'seeds', ns, 'cross', ncross, verdict)
    return lawO, res


def main():
    j, b, timeout = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    PA = [int(x) for x in sys.argv[4].split(',')]
    PB = [int(x) for x in sys.argv[5].split(',')]
    lawO, res = test_blocks(PA, PB, j, b, timeout)
    print('lawO', lawO)


if __name__ == '__main__':
    main()
