#!/usr/bin/env python3
# Emit one failing extension-property certificate per V-invariant graph mask on the
# proper nonempty clopen subsets of the Cantor set. Orbits of V on unordered pairs are
# the five Venn patterns; a mask is a union of orbits. A certificate is a family of K
# distinct sets (given by its atom configuration Q) and a target adjacency vector v
# that no clopen z outside the family realizes.
import itertools, json, sys

def valid(p):
    a, b, c, d = p
    return (a or b) and (c or d) and (a or c) and (b or d) and (b or c)

P = [p for p in itertools.product((0, 1), repeat=4) if valid(p)]
swap = lambda p: (p[0], p[2], p[1], p[3])
orbits, seen = [], set()
for p in P:
    if p in seen:
        continue
    o = sorted({p, swap(p)})
    seen |= set(o)
    orbits.append(o)
orb_of = {p: i for i, o in enumerate(orbits) for p in o}
NO = len(orbits)

E, F, M = 0, 1, 2
S_BIT = {E: 0, F: 1, M: 1}
T_BIT = {E: 1, F: 0, M: 1}

def configs(k):
    vecs = list(itertools.product((0, 1), repeat=k))
    for r in range(1, len(vecs) + 1):
        for Q in itertools.combinations(vecs, r):
            sets = [frozenset(j for j, v in enumerate(Q) if v[i]) for i in range(k)]
            if any(len(s) == 0 or len(s) == r for s in sets) or len(set(sets)) < k:
                continue
            yield Q, sets

def realized(Q, sets):
    r = len(Q)
    out = set()
    for col in itertools.product((E, F, M), repeat=r):
        if all(c == E for c in col) or all(c == F for c in col):
            continue
        if all(c != M for c in col) and frozenset(j for j in range(r) if col[j] == F) in sets:
            continue
        tup = []
        for s in sets:
            a = any(S_BIT[col[j]] for j in s)
            b = any(T_BIT[col[j]] for j in s)
            c = any(S_BIT[col[j]] for j in range(r) if j not in s)
            d = any(T_BIT[col[j]] for j in range(r) if j not in s)
            tup.append(orb_of[(int(a), int(b), int(c), int(d))])
        out.add(tuple(tup))
    return out

CONF = {k: [(Q, sets, realized(Q, sets)) for Q, sets in configs(k)] for k in (1, 2, 3)}
certs = []
for mask in range(1, 2 ** NO - 1):
    cert = None
    for k in (1, 2, 3):
        for Q, sets, T in CONF[k]:
            vecs = {tuple((mask >> o) & 1 for o in t) for t in T}
            missing = [v for v in itertools.product((0, 1), repeat=k) if v not in vecs]
            if missing:
                cert = {"mask": mask, "K": k, "atoms": [list(q) for q in Q], "v": list(missing[0])}
                break
        if cert:
            break
    certs.append(cert)
    print(json.dumps(cert))
print("MASKS", 2 ** NO - 2, "CERTIFIED", sum(1 for c in certs if c), file=sys.stderr)
