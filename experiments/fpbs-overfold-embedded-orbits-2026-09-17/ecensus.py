"""Exact deep_j versus law_j on levels satisfying (E) at depth j.

On an (E) level every same-fibre pair of Gamma_{j+1}(Q) whose two ends map
into ONE component of Gamma_j(Q) is lawful (that component has one vertex
over each point), so every overfold seed is cross-orbit.  This census asks
whether cross-orbit seeds ever beat law on such levels.

Sources of (E) levels
  cayley  : Cayley levels of 2-generated permutation groups <alpha, beta>
            (random pairs of degree d), deduplicated by the canonical BFS
            form of the marked Cayley graph; at j = 1, (E) holds iff
            <alpha, beta alpha beta^-2> is a proper subgroup.
  coset   : transitive levels Q = S\\G for the same groups, S = stabiliser
            of a point in the given permutation representation.
Every candidate is re-checked with elevels.e_defect.

Usage: python3 ecensus.py j maxn trials seed cap timeout_s
For each level: law exactly (lawful seeds only), then all seeds up to
min(law-1, cap).  Verdict: deep=law (complete to law-1), deep>=k (partial),
or COUNTEREXAMPLE.
"""
import os
import random
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-exact-c-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-relative-rank-2026-09-17'))
from elevels import e_defect, transitive, comp_defects  # noqa: E402
from export import instance_text  # noqa: E402

DEEP = os.environ.get('DEEP_BIN', os.path.join(HERE, 'deep'))


def compose(g, h):
    return tuple(h[g[i]] for i in range(len(g)))


def gen_group(al, be, cap):
    e = tuple(range(len(al)))
    els = [e]
    idx = {e: 0}
    i = 0
    while i < len(els):
        g = els[i]
        for s in (al, be):
            h = compose(g, s)
            if h not in idx:
                idx[h] = len(els)
                els.append(h)
                if len(els) > cap:
                    return None
        i += 1
    return els, idx


def cayley_level(al, be, cap):
    r = gen_group(al, be, cap)
    if r is None:
        return None
    els, idx = r
    PA = [idx[compose(g, al)] for g in els]
    PB = [idx[compose(g, be)] for g in els]
    return PA, PB


def canon_form(PA, PB, start=0):
    """BFS relabelling from `start`; equal forms = isomorphic marked sets."""
    n = len(PA)
    IA = [0] * n
    IB = [0] * n
    for i in range(n):
        IA[PA[i]] = i
        IB[PB[i]] = i
    lab = {start: 0}
    order = [start]
    i = 0
    while i < len(order):
        p = order[i]
        for P in (PA, IA, PB, IB):
            q = P[p]
            if q not in lab:
                lab[q] = len(order)
                order.append(q)
        i += 1
    if len(order) != n:
        return None
    return (tuple(lab[PA[p]] for p in order), tuple(lab[PB[p]] for p in order))


def iso_class(PA, PB):
    forms = [canon_form(PA, PB, s) for s in range(len(PA))]
    return min(f for f in forms if f is not None)


def run(inst, level, lawonly, timeout):
    with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False) as f:
        f.write(inst)
        path = f.name
    args = [DEEP, path, str(level)] + (['law'] if lawonly else [])
    try:
        out = subprocess.run(args, capture_output=True, text=True,
                             timeout=timeout).stdout
        done = True
    except subprocess.TimeoutExpired as ex:
        out = ex.stdout.decode() if isinstance(ex.stdout, bytes) else (ex.stdout or '')
        done = False
    os.unlink(path)
    m = re.search(r'level (\d+) GOAL', out)
    if m:
        return int(m.group(1)), done, out
    if 'level 0 goal' in out:
        return 0, done, out
    comp = [int(x) for x in re.findall(r'level (\d+): no goal', out)]
    return None, (max(comp) if comp else 0) if not done else 'none', out


def analyse(PA, PB, j, cap, timeout):
    inst = instance_text(PA, PB, j)
    V = int(inst.split()[0])
    if V > 256:
        return dict(V=V, skip='V>256')
    law, st, _ = run(inst, 40, True, timeout)
    if law is None:
        return dict(V=V, law=None)
    if law <= 1:
        return dict(V=V, law=law, deep=law, verdict='deep=law')
    lim = min(law - 1, cap)
    deep, st, out = run(inst, lim, False, timeout)
    if deep is not None:
        v = 'COUNTEREXAMPLE' if deep < law else 'deep=law'
        return dict(V=V, law=law, deep=deep, verdict=v)
    if st == 'none':
        v = 'deep=law' if lim == law - 1 else f'deep>={lim + 1}'
        return dict(V=V, law=law, verdict=v)
    return dict(V=V, law=law, verdict=f'deep>={st + 1} (timeout)')


def rand_pair(d, rng):
    a = list(range(d)); rng.shuffle(a)
    b = list(range(d)); rng.shuffle(b)
    return tuple(a), tuple(b)


def coset_level(al, be):
    return list(al), list(be)


def main():
    j, maxn, trials, seed, cap, timeout = [int(x) for x in sys.argv[1:7]]
    rng = random.Random(seed)
    seen = set()
    stats = {}
    for tr in range(trials):
        d = rng.randint(3, 8)
        al, be = rand_pair(d, rng)
        for kind in ('cayley', 'coset'):
            if kind == 'cayley':
                L = cayley_level(al, be, maxn)
            else:
                L = coset_level(al, be) if transitive(list(al), list(be)) else None
            if L is None:
                continue
            PA, PB = L
            if len(PA) > maxn or len(PA) < 3:
                continue
            key = iso_class(PA, PB)
            if key in seen:
                continue
            seen.add(key)
            if e_defect(PA, PB, j) != 0:
                continue
            reals, _ = comp_defects(PA, PB, j)
            r = analyse(PA, PB, j, cap, timeout)
            stats[r.get('verdict', r.get('skip', 'law?'))] = stats.get(
                r.get('verdict', r.get('skip', 'law?')), 0) + 1
            print(kind, 'n', len(PA), 'Lj-orbit sizes', sorted(reals),
                  'PA', PA, 'PB', PB, r)
            sys.stdout.flush()
    print('SUMMARY', stats)


if __name__ == '__main__':
    main()
