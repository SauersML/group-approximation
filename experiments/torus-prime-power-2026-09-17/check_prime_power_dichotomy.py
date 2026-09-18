"""Check the augmentation dichotomy for degree matrices over finite groups.

Part A (Bezout witness). For finite groups K with elements s, t of distinct prime
orders p, q, and integers a, b with a p + b q = 1, the element
D = a P_s + b P_t (P_s = sum of powers of s) has augmentation 1 and is a zero divisor
in Q[K]. We compute the rational rank of right multiplication by D on Q[K] exactly.

Part B (prime-power case). For random D in M_d(Z[P]) over small p-groups P with
epsilon(D) in GL_d(Z), right multiplication by D is invertible over F_p (hence D is
regular over Q). We check the rank of the reduction mod p.

Groups are given as permutation groups; elements are tuples.
"""
import random
from fractions import Fraction
from itertools import product


def compose(a, b):  # (a*b)(i) = a(b(i))
    return tuple(a[b[i]] for i in range(len(b)))


def closure(gens):
    n = len(gens[0])
    e = tuple(range(n))
    elems = {e}
    frontier = [e]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = compose(x, g)
                if y not in elems:
                    elems.add(y)
                    new.append(y)
        frontier = new
    return sorted(elems)


def order(g):
    e = tuple(range(len(g)))
    k, x = 1, g
    while x != e:
        x = compose(x, g)
        k += 1
    return k


def rank(rows, mod=None):
    m = [list(r) for r in rows]
    if mod is None:
        m = [[Fraction(v) for v in r] for r in m]
    r = 0
    ncols = len(m[0]) if m else 0
    for c in range(ncols):
        piv = None
        for i in range(r, len(m)):
            if (m[i][c] % mod if mod else m[i][c]) != 0:
                piv = i
                break
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        if mod:
            inv = pow(m[r][c] % mod, -1, mod)
            m[r] = [(v * inv) % mod for v in m[r]]
        else:
            pv = m[r][c]
            m[r] = [v / pv for v in m[r]]
        for i in range(len(m)):
            if i != r:
                f = m[i][c]
                if f != 0:
                    m[i] = [(vi - f * vr) % mod if mod else vi - f * vr
                            for vi, vr in zip(m[i], m[r])]
        r += 1
    return r


def right_mult_matrix(elems, D, d):
    """Matrix of xi -> xi D on Z[K]^d. D is a d x d list of dicts elem->coef."""
    idx = {g: i for i, g in enumerate(elems)}
    n = len(elems)
    rows = []
    for (g, i) in product(elems, range(d)):
        row = [0] * (n * d)
        # basis vector g e_i; (g e_i) D = sum_j g D_ij e_j
        for j in range(d):
            for h, c in D[i][j].items():
                row[idx[compose(g, h)] * d + j] += c
        rows.append(row)
    return rows


def bezout(p, q):
    for a in range(-q, q + 1):
        if (1 - a * p) % q == 0:
            return a, (1 - a * p) // q
    raise ValueError


def part_a():
    cyc = lambda n: tuple([(i + 1) % n for i in range(n)])
    groups = {
        "Z/6": [tuple(list(cyc(2)) + [2 + x for x in cyc(3)])],
        "Z/10": [tuple(list(cyc(2)) + [2 + x for x in cyc(5)])],
        "Z/15": [tuple(list(cyc(3)) + [3 + x for x in cyc(5)])],
        "S3": [(1, 0, 2), (1, 2, 0)],
        "A4": [(1, 2, 0, 3), (1, 0, 3, 2)],
        "S4": [(1, 0, 2, 3), (1, 2, 3, 0)],
    }
    for name, gens in groups.items():
        K = closure(gens)
        byord = {}
        for g in K:
            byord.setdefault(order(g), []).append(g)
        primes = [o for o in byord if o > 1 and all(o % k for k in range(2, o))]
        p, q = sorted(primes)[:2]
        s, t = byord[p][0], byord[q][0]
        a, b = bezout(p, q)
        D = {}
        x = tuple(range(len(s)))
        for _ in range(p):
            D[x] = D.get(x, 0) + a
            x = compose(x, s)
        x = tuple(range(len(t)))
        for _ in range(q):
            D[x] = D.get(x, 0) + b
            x = compose(x, t)
        eps = sum(D.values())
        rk = rank(right_mult_matrix(K, [[D]], 1))
        bound = len(K) - (len(K) - len(K) // p - len(K) // q)
        print(f"A {name:5s} |K|={len(K):3d} p={p} q={q} a={a} b={b} eps={eps} "
              f"rank_Q={rk} (<= {bound}) singular={rk < len(K)}")
        assert eps == 1 and rk < len(K) and rk <= bound


def part_b(trials=40):
    cyc = lambda n: tuple([(i + 1) % n for i in range(n)])
    pgroups = {
        "Z/4": (2, [cyc(4)]),
        "Z/2xZ/2": (2, [(1, 0, 2, 3), (0, 1, 3, 2)]),
        "D4": (2, [(1, 2, 3, 0), (0, 3, 2, 1)]),
        "Z/9": (3, [cyc(9)]),
        "Z/3xZ/3": (3, [tuple(list(cyc(3)) + [3, 4, 5]), (0, 1, 2, 4, 5, 3)]),
    }
    rng = random.Random(20260917)
    for name, (p, gens) in pgroups.items():
        P = closure(gens)
        worst = None
        for _ in range(trials):
            d = rng.choice([1, 2, 3])
            while True:
                D = [[{g: rng.randint(-3, 3) for g in rng.sample(P, min(3, len(P)))}
                      for _ in range(d)] for _ in range(d)]
                E = [[sum(D[i][j].values()) for j in range(d)] for i in range(d)]
                if rank(E) == d and abs(det(E)) == 1:
                    break
            M = right_mult_matrix(P, D, d)
            rp = rank(M, mod=p)
            rq = rank(M)
            assert rp == len(P) * d, (name, D)
            assert rq == len(P) * d
            worst = d
        print(f"B {name:8s} p={p}: {trials} random D with eps(D) in GL_d(Z): "
              f"all invertible mod p and regular over Q")


def det(E):
    d = len(E)
    if d == 1:
        return E[0][0]
    return sum((-1) ** j * E[0][j] * det([r[:j] + r[j + 1:] for r in E[1:]])
               for j in range(d))


if __name__ == "__main__":
    part_a()
    part_b()
    print("all checks passed")
