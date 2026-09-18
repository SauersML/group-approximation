#!/usr/bin/env python3
"""Prime (very elementary) unimodular dissections of the standard cone in R^3.

A dissection is a set of unimodular triangles (cones cone(a,b,c), |det|=1, a,b,c
primitive nonnegative) with disjoint interiors covering cone(e0,e1,e2).
Weight w(a,b,c) = 1/(h(a)h(b)h(c)), h = coordinate sum; weights of a dissection
sum to 1 (volume of the slice h <= 1).  A dissection is PRIME iff no set of
>= 2 but not all pieces has union a unimodular triangle.

modes:
  sanity
  bfs  fan|dis  MAXN REACH SECS      exhaustive over the local-move graph
  anneal LO HI SECS SEED             random search for prime fans of size in [LO,HI]
"""
import sys, random, time, itertools, math, json
from fractions import Fraction
from collections import defaultdict

E0, E1, E2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
DELTA = tuple(sorted((E0, E1, E2)))


def det(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def add(*vs):
    return tuple(sum(x) for x in zip(*vs))


def h(v):
    return v[0] + v[1] + v[2]


def tri(a, b, c):
    return tuple(sorted((a, b, c)))


def weight(t):
    return Fraction(1, h(t[0]) * h(t[1]) * h(t[2]))


PERMS = list(itertools.permutations(range(3)))


def canon(F):
    best = None
    for p in PERMS:
        G = tuple(sorted(tri(*[(v[p[0]], v[p[1]], v[p[2]]) for v in t]) for t in F))
        if best is None or G < best:
            best = G
    return best


def check(F):
    assert sum(weight(t) for t in F) == 1, "weight identity fails"
    for t in F:
        assert abs(det(*t)) == 1, "non-unimodular piece"


# ---------------- moves on fans ----------------
def edges_of(F):
    ed = defaultdict(list)
    for t in F:
        a, b, c = t
        ed[(a, b)].append(c)
        ed[(a, c)].append(b)
        ed[(b, c)].append(a)
    return ed


def fan_edge_blowup(F, e, ed):
    p, q = e
    u = add(p, q)
    G = set(F)
    for r in ed[e]:
        G.discard(tri(p, q, r))
        G.add(tri(p, u, r))
        G.add(tri(u, q, r))
    return frozenset(G)


def face_blowup(F, t):
    a, b, c = t
    u = add(a, b, c)
    G = set(F)
    G.discard(t)
    G |= {tri(a, b, u), tri(b, c, u), tri(c, a, u)}
    return frozenset(G)


def flops(F, ed):
    res = []
    for e, rs in ed.items():
        if len(rs) == 2:
            p, q = e
            a, b = rs
            if add(a, b) == add(p, q):
                res.append((e, a, b))
    return res


def do_flop(F, f):
    (p, q), a, b = f
    G = set(F)
    G.discard(tri(p, q, a))
    G.discard(tri(p, q, b))
    G.add(tri(a, b, p))
    G.add(tri(a, b, q))
    return frozenset(G)


def fan_blowdowns(F):
    star = defaultdict(list)
    for t in F:
        for v in t:
            star[v].append(t)
    res = []
    for u, ts in star.items():
        if u in DELTA:
            continue
        nbrs = set(v for t in ts for v in t if v != u)
        if len(ts) == 3 and len(nbrs) == 3 and add(*nbrs) == u:
            res.append(('Z', u, tuple(sorted(nbrs)), tuple(ts)))
        nl = sorted(nbrs)
        for i in range(len(nl)):
            for j in range(i + 1, len(nl)):
                p, q = nl[i], nl[j]
                if add(p, q) != u:
                    continue
                R = nbrs - {p, q}
                if len(ts) != 2 * len(R):
                    continue
                if all(tri(u, p, r) in F and tri(u, q, r) in F for r in R):
                    res.append(('E', u, (p, q), tuple(sorted(R))))
    return res


def do_fan_blowdown(F, bd):
    G = set(F)
    if bd[0] == 'Z':
        _, u, (a, b, c), ts = bd
        for t in ts:
            G.discard(t)
        G.add(tri(a, b, c))
    else:
        _, u, (p, q), R = bd
        for r in R:
            G.discard(tri(u, p, r))
            G.discard(tri(u, q, r))
            G.add(tri(p, q, r))
    return frozenset(G)


def fan_moves(F, grow):
    ed = edges_of(F)
    out = []
    if grow:
        out += [fan_edge_blowup(F, e, ed) for e in ed]
        out += [face_blowup(F, t) for t in F]
    out += [do_flop(F, f) for f in flops(F, ed)]
    out += [do_fan_blowdown(F, b) for b in fan_blowdowns(F)]
    return out


# ---------------- local (piecewise) moves on dissections ----------------
def dis_moves(F, grow):
    out = []
    Fs = set(F)
    if grow:
        for t in F:
            a, b, c = t
            for (p, q, r) in ((a, b, c), (a, c, b), (b, c, a)):
                u = add(p, q)
                G = set(Fs)
                G.discard(t)
                G.add(tri(p, u, r))
                G.add(tri(u, q, r))
                out.append(frozenset(G))
            out.append(face_blowup(F, t))
    side = defaultdict(list)          # full side {x,y} -> list of (triangle, opposite vertex)
    for t in F:
        a, b, c = t
        side[(a, b)].append((t, c))
        side[(a, c)].append((t, b))
        side[(b, c)].append((t, a))
    for (x, y), lst in side.items():
        if len(lst) != 2:
            continue
        (t1, o1), (t2, o2) = lst
        # flop across full side x-y
        if add(o1, o2) == add(x, y):
            G = set(Fs)
            G.discard(t1)
            G.discard(t2)
            G.add(tri(o1, o2, x))
            G.add(tri(o1, o2, y))
            out.append(frozenset(G))
        # merge (inverse edge split): side u-r with u = o1 + o2
        for u, r in ((x, y), (y, x)):
            if add(o1, o2) == u:
                G = set(Fs)
                G.discard(t1)
                G.discard(t2)
                G.add(tri(o1, o2, r))
                out.append(frozenset(G))
    # merge3 (inverse centre split)
    star = defaultdict(list)
    for t in F:
        for v in t:
            star[v].append(t)
    for u, ts in star.items():
        if u in DELTA:
            continue
        nbrs = set(v for t in ts for v in t if v != u)
        if len(ts) == 3 and len(nbrs) == 3 and add(*nbrs) == u:
            G = set(Fs)
            for t in ts:
                G.discard(t)
            G.add(tri(*nbrs))
            out.append(frozenset(G))
    return out


# ---------------- primality ----------------
def mu_pos(a, x, b):
    """b = lam*a + mu*x (coplanar); return mu > 0."""
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        m = a[i] * x[j] - a[j] * x[i]
        if m != 0:
            num = a[i] * b[j] - a[j] * b[i]
            return num * m > 0
    return False


def mergeable(F):
    Fl = list(F)
    total = len(Fl)
    W = {t: weight(t) for t in Fl}
    nb = defaultdict(set)
    for t in Fl:
        for v in t:
            for w in t:
                if v != w:
                    nb[v].add(w)
    V = list(nb)
    cand = set()
    for a in V:
        dirs = []
        for x in nb[a]:
            if not any(det(a, x, y) == 0 and mu_pos(a, y, x) for y in dirs):
                dirs.append(x)
        rays = []
        for x in dirs:
            rays.append([b for b in V if b != a and det(a, x, b) == 0 and mu_pos(a, x, b)])
        for i in range(len(rays)):
            for j in range(i + 1, len(rays)):
                for b in rays[i]:
                    for c in rays[j]:
                        if abs(det(a, b, c)) == 1:
                            cand.add(tri(a, b, c))
    out = []
    for T in cand:
        a, b, c = T
        D = det(a, b, c)
        cnt = 0
        ws = Fraction(0)
        for P in Fl:
            if all(det(x, b, c) * D >= 0 and det(a, x, c) * D >= 0 and det(a, b, x) * D >= 0 for x in P):
                cnt += 1
                ws += W[P]
        if 2 <= cnt < total and ws == weight(T):
            out.append(T)
    return out


def describe(F):
    V = sorted(set(v for t in F for v in t))
    return {"pieces": len(F), "vertices": len(V), "maxh": max(h(v) for v in V),
            "tris": [list(map(list, t)) for t in sorted(F)]}


# ---------------- drivers ----------------
def sanity():
    v01, v02, v12, c = (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)
    E = frozenset([tri(E0, v01, E2), tri(v01, E1, E2)])
    Z = frozenset([tri(E0, E1, c), tri(E1, E2, c), tri(E0, E2, c)])
    M = frozenset([tri(E0, v01, v02), tri(E1, v01, v12), tri(E2, v02, v12),
                   tri(v01, v12, c), tri(v12, v02, c), tri(v02, v01, c)])
    B6 = frozenset([tri(E0, v01, c), tri(v01, E1, c), tri(E1, v12, c), tri(v12, E2, c),
                    tri(E2, v02, c), tri(v02, E0, c)])
    for name, F in (("E", E), ("Z", Z), ("M", M), ("B6", B6)):
        check(F)
        print(name, "pieces", len(F), "mergeable proper subsets", len(mergeable(F)))


def bfs(kind, maxn, reach, secs):
    t0 = time.time()
    start = frozenset([DELTA])
    seen = {canon(start): start}
    frontier = [start]
    complete = True
    while frontier:
        if time.time() - t0 > secs:
            complete = False
            break
        new = []
        for F in frontier:
            grow = len(F) < reach
            moves = fan_moves(F, grow) if kind == "fan" else dis_moves(F, grow)
            for G in moves:
                if len(G) > reach:
                    continue
                k = canon(G)
                if k not in seen:
                    seen[k] = G
                    new.append(G)
        frontier = new
    bysize = defaultdict(int)
    primes = defaultdict(list)
    for k, F in seen.items():
        n = len(F)
        if n > maxn:
            continue
        check(F)
        bysize[n] += 1
        if n >= 2 and not mergeable(F):
            primes[n].append(F)
    print(json.dumps({"mode": "bfs", "kind": kind, "maxn": maxn, "reach": reach,
                      "complete_within_reach": complete, "secs": round(time.time() - t0, 1),
                      "count_by_size": dict(sorted(bysize.items())),
                      "primes_by_size": {n: len(v) for n, v in sorted(primes.items())}}))
    for n in sorted(primes):
        for F in primes[n][:6]:
            print("PRIME", json.dumps(describe(F)))


def anneal(lo, hi, secs, seed):
    rnd = random.Random(seed)
    t0 = time.time()
    found = {}
    steps = 0
    while time.time() - t0 < secs:
        F = frozenset([DELTA])
        target = rnd.randint(lo, hi)
        while len(F) < target:
            ed = edges_of(F)
            if rnd.random() < 0.6:
                F = fan_edge_blowup(F, rnd.choice(list(ed)), ed)
            else:
                F = face_blowup(F, rnd.choice(list(F)))
        s = len(mergeable(F))
        temp = 2.0
        for _ in range(4000):
            if time.time() - t0 > secs:
                break
            ed = edges_of(F)
            n = len(F)
            r = rnd.random()
            G = None
            if r < 0.5:
                fl = flops(F, ed)
                if fl:
                    G = do_flop(F, rnd.choice(fl))
            elif r < 0.75:
                bd = fan_blowdowns(F)
                if bd and n > lo:
                    G = do_fan_blowdown(F, rnd.choice(bd))
            elif r < 0.9:
                if n < hi:
                    G = fan_edge_blowup(F, rnd.choice(list(ed)), ed)
            else:
                if n < hi:
                    G = face_blowup(F, rnd.choice(list(F)))
            if G is None:
                continue
            steps += 1
            s2 = len(mergeable(G))
            if s2 <= s or rnd.random() < math.exp(-(s2 - s) / temp):
                F, s = G, s2
                if s == 0:
                    k = canon(F)
                    if k not in found:
                        check(F)
                        found[k] = F
            temp = max(0.1, temp * 0.999)
    sizes = defaultdict(int)
    for F in found.values():
        sizes[len(F)] += 1
    print(json.dumps({"mode": "anneal", "lo": lo, "hi": hi, "seed": seed, "steps": steps,
                      "prime_fans_by_size": dict(sorted(sizes.items()))}))
    shown = defaultdict(int)
    for F in sorted(found.values(), key=len):
        if shown[len(F)] < 2:
            shown[len(F)] += 1
            print("PRIME", json.dumps(describe(F)))


if __name__ == "__main__":
    m = sys.argv[1]
    if m == "sanity":
        sanity()
    elif m == "bfs":
        bfs(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]))
    elif m == "anneal":
        anneal(int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]))
