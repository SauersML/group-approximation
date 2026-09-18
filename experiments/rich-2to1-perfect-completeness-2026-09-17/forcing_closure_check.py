#!/usr/bin/env python3
"""Brute-force checks for perfect-completeness-rich-2to1-tractable-skeletons-are-in-p.

A 2-to-1 game: left alphabet [2k], right alphabet [k], every edge (u, v, pi)
with pi a list of length 2k mapping onto [k], each value taken exactly twice.

Checks:
  A. Forcing closure is sound: on every satisfying assignment L and every seed
     set S (|S| <= 2) of a small random satisfiable game, closure from L|S never
     conflicts and agrees with L on every vertex it labels.
  B. BKM right merge Psi(U): for random unique games U with alphabet 2k
     (k = 2, 3), Psi(U) is satisfiable iff U is, and when satisfiable one seed
     with the correct label forces its whole connected component.
  C. Grassmann skeleton over F_2^n (left: 2-subspaces, labels: linear
     functionals on them; right: nonzero vectors, labels: F_2): the forcing
     closure of t seeds is exactly the set of 2-subspaces of their span, so its
     mass is tiny, while Gaussian elimination recovers a satisfying labeling.
Exit code 0 iff every check passes.
"""
import itertools
import random
import sys

random.seed(20260917)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def pairings(twok):
    """All 2-to-1 maps [2k] -> [k] up to relabelling of [k], as lists."""
    out = []

    def rec(rem, blocks):
        if not rem:
            pi = [0] * twok
            for j, (a, b) in enumerate(blocks):
                pi[a] = j
                pi[b] = j
            out.append(pi)
            return
        a = rem[0]
        for b in rem[1:]:
            rec([x for x in rem if x not in (a, b)], blocks + [(a, b)])

    rec(list(range(twok)), [])
    return out


def closure(nl, nr, twok, edges, seeds):
    """Forcing closure. seeds: dict left->label. Returns (L, M, ok)."""
    adj_l = [[] for _ in range(nl)]
    adj_r = [[] for _ in range(nr)]
    for (u, v, pi) in edges:
        adj_l[u].append((v, pi))
        adj_r[v].append((u, pi))
    L = dict(seeds)
    M = {}
    queue = list(L.keys())
    while queue:
        u = queue.pop()
        for (v, pi) in adj_l[u]:
            val = pi[L[u]]
            if v in M:
                if M[v] != val:
                    return L, M, False
                continue
            M[v] = val
            for (w, piw) in adj_r[v]:
                if w in L:
                    if piw[L[w]] != M[v]:
                        return L, M, False
                    continue
                cand = set(range(twok))
                for (v2, pi2) in adj_l[w]:
                    if v2 in M:
                        cand &= {a for a in range(twok) if pi2[a] == M[v2]}
                if not cand:
                    return L, M, False
                if len(cand) == 1:
                    L[w] = cand.pop()
                    queue.append(w)
    for (u, v, pi) in edges:
        if u in L and v in M and pi[L[u]] != M[v]:
            return L, M, False
    return L, M, True


def satisfying(nl, nr, twok, edges):
    sols = []
    for L in itertools.product(range(twok), repeat=nl):
        M = {}
        ok = True
        for (u, v, pi) in edges:
            val = pi[L[u]]
            if M.setdefault(v, val) != val:
                ok = False
                break
        if ok:
            sols.append(L)
    return sols


# ---------------- A. soundness of forcing closure ----------------
def check_A():
    twok = 4
    P = pairings(twok)
    trials = 0
    for trial in range(60):
        nl, nr = 5, 6
        planted = [random.randrange(twok) for _ in range(nl)]
        rlab = [random.randrange(twok // 2) for _ in range(nr)]
        edges = []
        for u in range(nl):
            for v in random.sample(range(nr), 3):
                # pick a pairing mapping planted[u] to rlab[v]
                pi = random.choice(P)
                perm = list(range(twok // 2))
                random.shuffle(perm)
                pi = [perm[x] for x in pi]
                j = pi[planted[u]]
                pi = [rlab[v] if x == j else (j if x == rlab[v] else x) for x in pi]
                edges.append((u, v, pi))
        sols = satisfying(nl, nr, twok, edges)
        check(tuple(planted) in sols, "A planted solution not satisfying")
        for L in sols:
            for t in (1, 2):
                for S in itertools.combinations(range(nl), t):
                    CL, CM, ok = closure(nl, nr, twok, edges, {s: L[s] for s in S})
                    check(ok, "A closure conflicted on a true labeling")
                    for w, a in CL.items():
                        check(L[w] == a, "A closure disagrees with a satisfying labeling")
                    trials += 1
    print("A: closure soundness checked on", trials, "(labeling, seed set) pairs")


# ---------------- B. BKM right merge ----------------
def psi(nl, nr, twok, ug_edges):
    """ug_edges: (u, v, phi) phi a permutation of [2k]. Right vertex (v, sigma)."""
    P = pairings(twok)
    edges = []
    for (u, v, phi) in ug_edges:
        for s, sigma in enumerate(P):
            edges.append((u, v * len(P) + s, [sigma[phi[a]] for a in range(twok)]))
    return nl, nr * len(P), edges


def ug_satisfiable(nl, nr, twok, ug_edges):
    for L in itertools.product(range(twok), repeat=nl):
        M = {}
        ok = True
        for (u, v, phi) in ug_edges:
            val = phi[L[u]]
            if M.setdefault(v, val) != val:
                ok = False
                break
        if ok:
            return L
    return None


def components(nl, nr, edges):
    parent = list(range(nl + nr))

    def f(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for (u, v, _) in edges:
        parent[f(u)] = f(nl + v)
    comp = {}
    for u in range(nl):
        comp.setdefault(f(u), []).append(u)
    return list(comp.values())


def check_B():
    counts = {True: 0, False: 0}
    for twok in (4, 6):
        for trial in range(40):
            nl, nr = 4, 3
            planted = random.random() < 0.5
            L0 = [random.randrange(twok) for _ in range(nl)]
            M0 = [random.randrange(twok) for _ in range(nr)]
            ug = []
            for u in range(nl):
                for v in random.sample(range(nr), 2):
                    phi = list(range(twok))
                    random.shuffle(phi)
                    if planted:
                        j = phi.index(M0[v])
                        phi[j], phi[L0[u]] = phi[L0[u]], phi[j]
                    ug.append((u, v, phi))
            solU = ug_satisfiable(nl, nr, twok, ug)
            pl, pr, pe = psi(nl, nr, twok, ug)
            solP = satisfying(pl, pr, twok, pe)
            check((solU is not None) == bool(solP), "B satisfiable(Psi(U)) != satisfiable(U)")
            counts[solU is not None] += 1
            if solU is not None:
                for comp in components(pl, pr, pe):
                    s = comp[0]
                    CL, CM, ok = closure(pl, pr, twok, pe, {s: solU[s]})
                    check(ok, "B closure conflicted on Psi(U)")
                    check(set(CL.keys()) == set(comp), "B one seed did not force its component")
    print("B: Psi(U) satisfiability equivalence on", counts[True], "satisfiable and",
          counts[False], "unsatisfiable unique games; one-seed closure = component")


# ---------------- C. Grassmann skeleton ----------------
def check_C():
    for n in (4, 5, 6):
        vecs = list(range(1, 2 ** n))
        subs = set()
        for x in vecs:
            for y in vecs:
                if x < y:
                    subs.add(tuple(sorted((x, y, x ^ y))))
        subs = sorted(subs)
        idx = {v: i for i, v in enumerate(vecs)}
        g = random.randrange(1, 2 ** n)  # global functional f(x) = <g, x>

        def f(x):
            return bin(g & x).count("1") % 2

        edges = []
        planted = []
        for li, (b1, b2, b3) in enumerate(subs):
            planted.append(2 * f(b1) + f(b2))
            for x in (b1, b2, b3):
                c = [(a >> 1, a & 1) for a in range(4)]
                if x == b1:
                    pi = [c1 for (c1, c2) in c]
                elif x == b2:
                    pi = [c2 for (c1, c2) in c]
                else:
                    pi = [c1 ^ c2 for (c1, c2) in c]
                edges.append((li, idx[x], pi))
        nl, nr = len(subs), len(vecs)
        E = len(edges)
        for t in (1, 2):
            best = 0
            samples = list(itertools.combinations(range(nl), t))
            if len(samples) > 400:
                samples = random.sample(samples, 400)
            for S in samples:
                CL, CM, ok = closure(nl, nr, 4, edges, {s: planted[s] for s in S})
                check(ok, "C closure conflicted on planted labeling")
                span = {0}
                for s in S:
                    for x in subs[s]:
                        span |= {y ^ x for y in span}
                inside = {li for li, sb in enumerate(subs) if set(sb) <= span}
                check(set(CL.keys()) == inside, "C closure != subspaces of span")
                best = max(best, 3 * len(CL) / E)
            print("C: n=%d t=%d max forcing-closure mass %.4f (%d left vertices)" % (n, t, best, nl))
        # Gaussian elimination on the affine label system. Add random affine
        # offsets on right labels (so the all-zero labeling is not a solution),
        # write every edge as a linear equation over F_2 in the label bits,
        # solve, and confirm the solution satisfies every edge.
        off = [random.randrange(2) for _ in vecs]
        nv = 2 * nl + nr
        eqs = []
        aff_edges = []
        for (li, xi, pi) in edges:
            # pi(a) is c1, c2 or c1 ^ c2 for a = 2*c1 + c2
            coeff = 0
            if pi[2] != pi[0]:
                coeff |= 1 << (2 * li)
            if pi[1] != pi[0]:
                coeff |= 1 << (2 * li + 1)
            coeff |= 1 << (2 * nl + xi)
            eqs.append((coeff, off[xi]))
            aff_edges.append((li, xi, [b ^ off[xi] for b in pi]))
        pivots = {}
        consistent = True
        for (m, b) in eqs:
            while m:
                h = m.bit_length() - 1
                if h in pivots:
                    pm, pb = pivots[h]
                    m ^= pm
                    b ^= pb
                else:
                    pivots[h] = (m, b)
                    break
            else:
                if b:
                    consistent = False
        check(consistent, "C affine system inconsistent")
        sol = [0] * nv
        for h in sorted(pivots):
            m, b = pivots[h]
            val = b
            for j in range(h):
                if (m >> j) & 1:
                    val ^= sol[j]
            sol[h] = val
        good = all(pi[2 * sol[2 * li] + sol[2 * li + 1]] == sol[2 * nl + xi]
                   for (li, xi, pi) in aff_edges)
        check(good, "C elimination solution does not satisfy the affine skeleton")
        print("C: n=%d Gaussian elimination returns a satisfying labeling of the offset skeleton: %s" % (n, good))


check_A()
check_B()
check_C()
print("ALL PASS" if not FAIL else "FAILURES: %d" % len(FAIL))
sys.exit(1 if FAIL else 0)
