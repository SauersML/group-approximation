#!/usr/bin/env python3
"""Model test for the crossing-pair criterion (lane hl-lot-torsion, 2026-09-14).

Claim under test. Let Gamma be a reduced LOT (edges (i, l, t), relator i l t^-1 l^-1) whose
graph T(Gamma) (one edge {i(e), l(e)} per edge e) has cyclomatic number 2 and contains a
crossing pair e = (v, u, t_e), f = (u, v, t_f) with t_e != t_f. Let T1 be T - {e, f} with v
identified to u (cyclomatic number 1). If some edge s on the cycle of T1 has F = T1 - s a forest
in which t_e (or t_f) lies in a component containing neither u nor the other of t_e, t_f, then
eliminating v via e gives a presentation satisfying Barreto--Minian Theorem 2.5 with s omitted.

Checks, all against the census code already on main (lot.py, lot2.py, lot4.py):
 1. predicted minima multisets after the elimination equal the computed ones;
 2. predicted concatenability (criterion) agrees with the computed one, for every crossing pair
    and every omitted relator, including the failing cases (negative controls);
 3. every LOT passing the criterion passes lot2.test_bm25 on the eliminated presentation.
Run: python3 crossing_pair_check.py 300000  (seeded; the census modules and data are read
from ../lot-asphericity-census on main).
"""
import os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
CENSUS = os.path.join(HERE, '..', 'lot-asphericity-census')
sys.path.insert(0, CENSUS)
from collections import Counter
from lot import rel
from lot2 import minima, concat_order, verify_concat, test_bm25
from lot4 import eliminate

def cyclo(verts, edges):
    p = {x: x for x in verts}
    def f(x):
        while p[x] != x:
            p[x] = p[p[x]]; x = p[x]
        return x
    for a, b in edges:
        p[f(a)] = f(b)
    return len(edges) - len(verts) + len({f(x) for x in verts})

def components(verts, edges):
    p = {x: x for x in verts}
    def f(x):
        while p[x] != x:
            p[x] = p[p[x]]; x = p[x]
        return x
    for a, b in edges:
        p[f(a)] = f(b)
    return f

def is_reduced(n, E):
    deg = Counter()
    for (i, l, t) in E:
        if l == i or l == t: return False
        deg[i] += 1; deg[t] += 1
    labels = {l for (_, l, _) in E}
    if any(deg[v] == 1 and v not in labels for v in range(n)): return False
    for v in range(n):
        out_l = [l for (i, l, t) in E if i == v]
        in_l = [l for (i, l, t) in E if t == v]
        if len(out_l) != len(set(out_l)) or len(in_l) != len(set(in_l)): return False
    return True

def crossing_witnesses(n, E):
    """Yield (ke, kf, ks, predicted_pass) for every crossing pair (e, f) and every relator s != e."""
    T = [(i, l) for (i, l, t) in E]
    if cyclo(range(n), T) != 2: return
    for ke, (v, u, te) in enumerate(E):
        for kf, (i2, l2, tf) in enumerate(E):
            if kf == ke or i2 != u or l2 != v: continue
            verts = [x for x in range(n) if x != v]
            idmap = lambda x: u if x == v else x
            for ks in range(len(E)):
                if ks == ke: continue
                if ks == kf:
                    yield ke, kf, ks, False       # Q omitted: forest would need c(T) <= 1
                    continue
                F = [(idmap(a), idmap(b)) for k, (a, b) in enumerate(T) if k not in (ke, kf, ks)]
                forest = cyclo(verts, F) == 0 and all(a != b for a, b in F)
                ok = False
                if forest and te != tf:
                    root = components(verts, F)
                    ok = (root(te) != root(u) and root(te) != root(tf)) or \
                         (root(tf) != root(u) and root(tf) != root(te))
                yield ke, kf, ks, ok

def predicted_minima(E, ke, kf):
    v, u, te = E[ke]; tf = E[kf][2]
    out = []
    for k, (i, l, t) in enumerate(E):
        if k == ke: continue
        if k == kf: out.append(Counter([u, u, te, tf])); continue
        a, b = (u if i == v else i), (u if l == v else l)
        out.append(Counter({a: 1, b: 1}) if a != b else Counter({a: 2}))
    return out

def check_lot(n, E, stats):
    rels = [rel(e) for e in E]
    passed_any = False
    for ke, kf, ks, pred in crossing_witnesses(n, E):
        v = E[ke][0]
        gens, R = eliminate(tuple(range(n)), rels, ke, v)
        comp = [minima(r) for r in R]
        predm = predicted_minima(E, ke, kf)
        if comp != predm:
            stats['minima_mismatch'] += 1
            print('MINIMA MISMATCH', E, ke, kf, comp, predm); continue
        # relator index ks in the eliminated list
        idx = ks if ks < ke else ks - 1
        sub = [comp[j] for j in range(len(comp)) if j != idx]
        o = concat_order(sub)
        actual = o is not None and verify_concat(sub, o)
        stats['pairs'] += 1
        if actual != pred:
            stats['disagree'] += 1
            print('DISAGREE', E, 'e', ke, 'f', kf, 's', ks, 'pred', pred, 'actual', actual)
        if pred:
            passed_any = True
            gidx = {g: r for r, g in enumerate(gens)}
            RR = [[(gidx[g], e) for (g, e) in r] for r in R]
            if not test_bm25(len(gens), RR):
                stats['bm25_fail_on_pass'] += 1
                print('BM25 FAIL ON PASS', E, ke, kf, ks)
    return passed_any

def random_lot(n, rng):
    prufer = [rng.randrange(n) for _ in range(n - 2)]
    deg = [1] * n
    for x in prufer: deg[x] += 1
    edges = []
    for x in prufer:
        leaf = min(i for i in range(n) if deg[i] == 1)
        edges.append((leaf, x)); deg[leaf] -= 1; deg[x] -= 1
    a, b = [i for i in range(n) if deg[i] == 1]
    edges.append((a, b))
    E = []
    for (a, b) in edges:
        if rng.random() < 0.5: a, b = b, a
        E.append((a, rng.randrange(n), b))
    return E

def main():
    stats = Counter()
    import json
    hard = [json.loads(line) for line in open(os.path.join(CENSUS, 'outp57', 'survivorsp4_n7.jsonl'))]
    hard_pass = 0
    for d in hard:
        E = [tuple(e) for e in d['lot']]
        Erev = [(t, l, i) for (i, l, t) in E]
        p = check_lot(7, E, stats) or check_lot(7, Erev, stats)
        hard_pass += p
    print('hard seven-vertex classes passing criterion (T or I side):', hard_pass, 'of', len(hard))
    rng = random.Random(20260914)
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    covered = Counter()
    for _ in range(samples):
        n = rng.choice([8, 9, 10])
        E = random_lot(n, rng)
        if not is_reduced(n, E): continue
        stats['reduced'] += 1
        cT = cyclo(range(n), [(i, l) for (i, l, t) in E]); cI = cyclo(range(n), [(l, t) for (i, l, t) in E])
        Erev = [(t, l, i) for (i, l, t) in E]
        pT = check_lot(n, E, stats); pI = check_lot(n, Erev, stats)
        if cT >= 2 and cI >= 2:
            covered['not_cor31'] += 1
            if (cT == 2 or cI == 2): covered['some_side_c2'] += 1
            if pT or pI: covered['criterion'] += 1
    print('stats', dict(stats)); print('coverage among reduced samples', dict(covered))

if __name__ == '__main__':
    main()
