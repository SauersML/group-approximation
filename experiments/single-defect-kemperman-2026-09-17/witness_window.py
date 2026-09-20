"""Finite-window check of Steps 4-5 of
research/torsion-free-single-defect-rules-need-strict-linear-parts-proof.md.

Host G = Z^2 (torsion-free). For random memories M, patterns p, arbitrary fields w with w|_M != 0,
and q = 3, build the events A_g, B_g for g in a box F, solve the capacity-(q-1) matching and a
background x, and verify that (W1)-(W3) hold on F by direct evaluation.

It also runs the same code on the torsion host Z/2 x Z with M = {(0,0),(1,0)}, where the translate
g = (1,0) has gM = M. The events there are unavoidable and the matching fails: the boundary case.
"""
import itertools
import random

import networkx as nx


def run(q, M, p, w, F, add):
    Mset = set(M)
    fixed = {m: p[i] for i, m in enumerate(M)}
    events = []  # (g, {h: value}) restricted to free coordinates
    for g in F:
        gM = [add(g, m) for m in M]
        for kind in "AB":
            pres = {}
            for i, h in enumerate(gM):
                v = p[i] if kind == "A" else (p[i] - t * w(h)) % q
                pres[h] = v
            if any(h in Mset and pres[h] != fixed[h] for h in gM):
                continue  # impossible event
            free = {h: v for h, v in pres.items() if h not in Mset}
            events.append((g, kind, free))
    if any(not free for _, _, free in events):
        return None, "unavoidable event (translate inside M)"
    # capacity matching via max flow
    G = nx.DiGraph()
    for k, (_, _, free) in enumerate(events):
        G.add_edge("s", ("e", k), capacity=1)
        for h in free:
            G.add_edge(("e", k), ("h", h), capacity=1)
    for k, (_, _, free) in enumerate(events):
        for h in free:
            G.add_edge(("h", h), "t", capacity=q - 1)
    val, flow = nx.maximum_flow(G, "s", "t")
    if val < len(events):
        return None, "Hall fails"
    x = dict(fixed)
    forb = {}
    for k, (_, _, free) in enumerate(events):
        for h in free:
            if flow[("e", k)].get(("h", h), 0) == 1:
                forb.setdefault(h, set()).add(free[h])
    for h, vs in forb.items():
        x[h] = min(set(range(q)) - vs)
    xv = lambda h: x.get(h, 0)
    # verify
    for g in F:
        gM = [add(g, m) for m in M]
        assert tuple(xv(h) for h in gM) != tuple(p), ("A", g)
        assert tuple((xv(h) + t * w(h)) % q for h in gM) != tuple(p), ("B", g)
    return x, "ok"


random.seed(1)
t = 1
ok = 0
add2 = lambda a, b: (a[0] + b[0], a[1] + b[1])
for trial in range(200):
    q = 3
    k = random.randint(2, 5)
    box = [(i, j) for i in range(-2, 3) for j in range(-2, 3)]
    M = random.sample(box, k)
    p = [random.randrange(q) for _ in M]
    table = {}
    def w(h, table=table):
        if h not in table:
            table[h] = random.randrange(q)
        return table[h]
    table[M[0]] = 1  # force w|_M != 0
    F = [(i, j) for i in range(-6, 7) for j in range(-6, 7) if (i, j) != (0, 0)]
    x, msg = run(q, M, p, w, F, add2)
    assert msg == "ok", msg
    ok += 1
print(f"Z^2, q=3: {ok}/200 random windows admit a witness background")

# torsion boundary: Z/2 x Z, M = {(0,0),(1,0)}
addt = lambda a, b: ((a[0] + b[0]) % 2, a[1] + b[1])
M = [(0, 0), (1, 0)]
p = [0, 0]
w = lambda h: 1 if h == (0, 0) else 0
F = [(i, j) for i in range(2) for j in range(-4, 5) if (i, j) != (0, 0)]
print("Z/2 x Z, M = subgroup coset:", run(3, M, p, w, F, addt)[1])

# part (b): torsion host Z/3 x Z/3 x Z, q >= 2|M|+1, M with trivial stabiliser
add3 = lambda a, b: ((a[0] + b[0]) % 3, (a[1] + b[1]) % 3, a[2] + b[2])
ok = 0
elems = [(i, j, k) for i in range(3) for j in range(3) for k in range(-1, 2)]
for trial in range(200):
    k = random.randint(2, 3)
    q = 2 * k + 1 if 2 * k + 1 in (5, 7) else 7
    while True:
        M = random.sample(elems, k)
        stab = [g for g in elems if g != (0, 0, 0) and set(add3(g, m) for m in M) == set(M)]
        if not stab:
            break
    p = [random.randrange(q) for _ in M]
    table = {M[0]: 1}
    def w(h, table=table, q=q):
        if h not in table:
            table[h] = random.randrange(q)
        return table[h]
    F = [(i, j, l) for i in range(3) for j in range(3) for l in range(-5, 6) if (i, j, l) != (0, 0, 0)]
    x, msg = run(q, M, p, w, F, add3)
    assert msg == "ok", msg
    ok += 1
print(f"Z/3 x Z/3 x Z, q = 2|M|+1, trivial stabiliser: {ok}/200 windows admit a witness background")
