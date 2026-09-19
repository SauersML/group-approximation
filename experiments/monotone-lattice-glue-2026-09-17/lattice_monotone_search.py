"""Exhaustive check over Z, window {0,1}: monotone injective automata on small non-chain lattices.

For each alphabet L (a finite poset given by its order relation) we enumerate every rule
f : L x L -> L that is monotone for the product order and fixes the constants (f(d,d) = d).
rho(x)_n = f(x_n, x_{n+1}).  Injectivity on L^Z is decided by the pair graph: vertices (a,b),
edge (a,b)->(a',b') when f(a,a') = f(b,b').  rho is injective iff every vertex lying on a
bi-infinite path is diagonal.

For every injective rule we record whether it is a copy of one coordinate, and, for the Boolean
square, whether it is a layerwise translation.
"""
import itertools, sys

def poset(elems, rel):
    le = {(a, b): (a == b) or ((a, b) in rel) for a in elems for b in elems}
    # transitive closure
    changed = True
    while changed:
        changed = False
        for a in elems:
            for b in elems:
                if not le[(a, b)]:
                    for m in elems:
                        if le[(a, m)] and le[(m, b)]:
                            le[(a, b)] = True; changed = True; break
    return le

def monotone_rules(elems, le):
    inputs = list(itertools.product(elems, repeat=2))
    # order inputs so that predecessors come first (by number of elements below)
    below = {d: sum(le[(e, d)] for e in elems) for d in elems}
    inputs.sort(key=lambda p: below[p[0]] + below[p[1]])
    idx = {p: i for i, p in enumerate(inputs)}
    preds = []
    for p in inputs:
        preds.append([idx[q] for q in inputs if q != p and le[(q[0], p[0])] and le[(q[1], p[1])]])
    covers = [(a, b) for a in elems for b in elems if a != b and le[(a, b)]
              and not any(m not in (a, b) and le[(a, m)] and le[(m, b)] for m in elems)]
    val = [None] * len(inputs)
    out = []
    stats = {'monotone': 0}
    def rec(k):
        if k == len(inputs):
            stats['monotone'] += 1
            f = dict(zip(inputs, val))
            # necessary condition (item 3 of monotone-strict-automata-ascend-along-poset-homs):
            # on every cover {a,b} the rule is a copy of one coordinate
            for (a, b) in covers:
                if not ((f[(a, b)] == a and f[(b, a)] == b) or (f[(a, b)] == b and f[(b, a)] == a)):
                    return
            if injective(elems, f):
                out.append(f)
            return
        p = inputs[k]
        cands = [p[0]] if p[0] == p[1] else elems
        for v in cands:
            if all(le[(val[j], v)] for j in preds[k]):
                val[k] = v
                rec(k + 1)
        val[k] = None
    rec(0)
    return stats['monotone'], out

def injective(elems, f):
    V = [(a, b) for a in elems for b in elems]
    E = {v: [] for v in V}
    R = {v: [] for v in V}
    for (a, b) in V:
        for a2 in elems:
            for b2 in elems:
                if f[(a, a2)] == f[(b, b2)]:
                    E[(a, b)].append((a2, b2)); R[(a2, b2)].append((a, b))
    alive = set(V)
    changed = True
    while changed:
        changed = False
        for v in list(alive):
            if not any(w in alive for w in E[v]) or not any(w in alive for w in R[v]):
                alive.discard(v); changed = True
    return all(a == b for (a, b) in alive)

def is_copy(elems, f):
    return all(f[(a, b)] == a for a in elems for b in elems) or all(f[(a, b)] == b for a in elems for b in elems)

def run(name, elems, rel, c, sides=None):
    le = poset(elems, rel)
    nrules, inj = monotone_rules(elems, le)
    copies = sum(is_copy(elems, f) for f in inj)
    print(f"{name}: |L|={len(elems)} monotone idempotent rules={nrules} injective={len(inj)} copies={copies}", flush=True)
    return le, inj

if __name__ == "__main__":
    # Boolean square 2x2: letters 00,01,10,11
    sq = ['00', '01', '10', '11']
    sq_rel = {('00', '01'), ('00', '10'), ('01', '11'), ('10', '11')}
    le, inj = run("2x2", sq, sq_rel, '00')
    layer = 0
    for f in inj:
        ok = False
        for s1 in (0, 1):
            for s2 in (0, 1):
                if all(f[(a, b)] == ((a, b)[s1][0] + (a, b)[s2][1]) for a in sq for b in sq):
                    ok = True
        layer += ok
    print(f"  2x2 injective rules that are layerwise translations: {layer} of {len(inj)}")
    # M3: 0 < a,b,e < 1
    m3 = ['0', 'a', 'b', 'e', '1']
    m3_rel = {('0', x) for x in 'abe'} | {(x, '1') for x in 'abe'}
    run("M3", m3, m3_rel, 'a')
    # N5: 0 < a < b < 1, 0 < e < 1
    n5 = ['0', 'a', 'b', 'e', '1']
    n5_rel = {('0', 'a'), ('a', 'b'), ('b', '1'), ('0', 'e'), ('e', '1')}
    run("N5", n5, n5_rel, 'a')
    # V shape: 0 < a, 0 < b
    v = ['0', 'a', 'b']
    run("V", v, {('0', 'a'), ('0', 'b')}, '0')
    # bowtie: p,q < r,s
    bt = ['p', 'q', 'r', 's']
    run("bowtie", bt, {('p', 'r'), ('p', 's'), ('q', 'r'), ('q', 's')}, 'p')
    # 1 + 2x2 (down-set lattice of V)
    os_ = ['z'] + sq
    run("1+2x2", os_, sq_rel | {('z', '00')}, '00')
