#!/usr/bin/env python3
"""Independent control of coset.py by direct evaluation on finite permutation groups.

Shares no code with coset.py.  Two checks.
 (1) Lemma check: random rules, placements and elements q; with U = <q>, whenever every block
     C of the left-coset partition of M satisfies mu(1_C) = mu(0000) (resp. the complement
     condition), evaluate tau(1_U) and tau(0) (resp. tau(1 - 1_U) and tau(1)) at every group
     element and confirm equality.
 (2) Witness check: for every rule killed in coset.json, random placements whose realized
     quotient partition coarsens a blocking partition P; with the recorded pair (i, j) and
     U = <m_i^-1 m_j>, confirm that either M lies in U (cyclic memory) or the collision holds.
Usage: control.py coset.json ../gottschalk-four-address-balance/flip1.json
"""
import itertools, json, random, sys

random.seed(20260917)


def compose(p, q):  # (p*q)(x) = p(q(x)) ; group law g*h acts h first
    return tuple(p[i] for i in q)


def inv(p):
    r = [0] * len(p)
    for i, v in enumerate(p):
        r[v] = i
    return tuple(r)


def closure(gens):
    e = tuple(range(len(gens[0])))
    seen = {e}
    frontier = [e]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = compose(g, s)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return sorted(seen)


def cyc(n, k):
    return tuple((i + k) % n for i in range(n))


def groups():
    out = []
    # S_4, S_5, A_5, dihedral D_12, Z_2 x S_4 (on 6 points), PSL-like: S_3 x S_3
    out.append(("S4", closure([(1, 0, 2, 3), (1, 2, 3, 0)])))
    out.append(("S5", closure([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)])))
    out.append(("A5", closure([(1, 2, 0, 3, 4), (0, 1, 3, 4, 2), (1, 0, 3, 2, 4)])))
    out.append(("D12", closure([cyc(12, 1), tuple((-i) % 12 for i in range(12))])))
    out.append(("S3xS3", closure([(1, 0, 2, 3, 4, 5), (1, 2, 0, 3, 4, 5),
                                   (0, 1, 2, 4, 3, 5), (0, 1, 2, 4, 5, 3)])))
    out.append(("Z2xS4", closure([(1, 0, 2, 3, 4, 5), (1, 2, 3, 0, 4, 5), (0, 1, 2, 3, 5, 4)])))
    return out


def ev(mu, bits):
    return (mu >> (bits[0] | bits[1] << 1 | bits[2] << 2 | bits[3] << 3)) & 1


def tau(mu, G, M, x):
    return {g: ev(mu, [x[compose(g, m)] for m in M]) for g in G}


def cyclic(q):
    e = tuple(range(len(q)))
    S, h = {e}, q
    while h != e:
        S.add(h)
        h = compose(h, q)
    return S


def left_blocks(M, U):
    blocks = []
    for i, m in enumerate(M):
        for b in blocks:
            if compose(inv(M[b[0]]), m) in U:
                b.append(i)
                break
        else:
            blocks.append([i])
    return blocks


def collision(mu, G, M, U, blocks):
    z, o = ev(mu, [0] * 4), ev(mu, [1] * 4)
    ind = lambda C: [1 if i in C else 0 for i in range(4)]
    A = all(ev(mu, ind(C)) == z for C in blocks)
    B = all(ev(mu, [1 - t for t in ind(C)]) == o for C in blocks)
    res = []
    if A:
        x = {g: (1 if g in U else 0) for g in G}
        res.append(tau(mu, G, M, x) == tau(mu, G, M, {g: 0 for g in G}))
    if B:
        x = {g: (0 if g in U else 1) for g in G}
        res.append(tau(mu, G, M, x) == tau(mu, G, M, {g: 1 for g in G}))
    return A or B, res


PAIRS = [(i, j) for i in range(4) for j in range(4) if i != j]


def realized(M):
    q = [compose(inv(M[i]), M[j]) for (i, j) in PAIRS]
    lab, keys = [], {}
    for v in q:
        keys.setdefault(v, len(keys))
        lab.append(keys[v])
    return lab


def coarsens(Q, P):
    cls = {}
    for a, b in zip(P, Q):
        cls.setdefault(a, set()).add(b)
    return all(len(s) == 1 for s in cls.values())


def main():
    cj = json.load(open(sys.argv[1]))
    parts = json.load(open(sys.argv[2]))["partitions"]
    Gs = groups()
    n1 = n1c = 0
    for name, G in Gs:
        e = G[0] if G[0] == tuple(range(len(G[0]))) else tuple(range(len(G[0])))
        for _ in range(150):
            mu = random.randrange(1 << 16)
            rest = random.sample([g for g in G if g != e], 3)
            M = [e] + rest
            q = random.choice(G)
            U = cyclic(q)
            ok, res = collision(mu, G, M, U, left_blocks(M, U))
            if ok:
                n1 += 1
                n1c += all(res)
                assert all(res), (name, mu, M, q)
    n2 = n2cyc = n2col = 0
    killed = cj["killed"]
    covered = set()
    for name, G in Gs:
        e = tuple(range(len(G[0])))
        nonid = [g for g in G if g != e]
        for _ in range(4000 if len(G) <= 72 else 1500):
            M = [e] + random.sample(nonid, 3)
            Q = realized(M)
            for r, wit in killed.items():
                mu = int(r)
                for P, (i, j) in wit.items():
                    if not coarsens(Q, parts[int(P)]):
                        continue
                    U = cyclic(compose(inv(M[i]), M[j]))
                    n2 += 1
                    if all(m in U for m in M):
                        n2cyc += 1
                        continue
                    ok, res = collision(mu, G, M, U, left_blocks(M, U))
                    assert ok and all(res), (name, r, P, M)
                    n2col += 1
                    covered.add(r)
    print("lemma checks with a predicted collision:", n1, "confirmed:", n1c)
    print("witness checks:", n2, "cyclic memory:", n2cyc, "collisions confirmed:", n2col)
    print("killed rules exercised by a confirmed collision:", len(covered), "of", len(killed))


if __name__ == "__main__":
    main()
