#!/usr/bin/env python3
"""Checks for the end-measure obstruction to shift-normalizing enumerations.

Part 1. Solvability of the end-measure equations for a finite graph of
groups with finite edge groups. Unknowns: T = mu(closure of P) and x_e for
each oriented edge of the quotient graph, with
    x_e + x_ebar = T                                   (every edge)
    T = n_v + sum_{e out of v} (|G_v|/|G_e|) x_e        (every finite vertex)
and no equation at a one-ended vertex. Here edge 0 is subdivided and its
midpoint (stabilizer G_e0) is the base vertex v0 of the orbit map
y -> v0.y, so n_v = |G_e0| at the midpoint and n_v = 0 elsewhere.
Exact rational Gaussian elimination.
The claim predicts: solvable iff some vertex group is infinite or chi != 0,
and unsolvable for the two-ended examples.

Part 2. Brute-force sanity check in F_2 = <a,b>. Left Cayley convention: the
ends are left-infinite words, the depth-1 pieces are U_x = {reduced words
ending in x}. For an automorphism phi and multipliers c_x (|c_x| <= 2) put
sigma(y) = phi(y) c_x on U_x. Among the maps that are exactly injective on
B_5 and exactly one-to-one on the shells 3..5, count the uncovered points of
B_5 and subtract the one point e outside the pieces. That is the number of
missed points, i.e. minus the near index; the claim predicts it is always 0.
For Z the same search finds nonzero values.
"""
from fractions import Fraction
from itertools import product


# ---------------------------------------------------------------- part 1
def solvable(rows):
    """rows: list of (coeff dict, rhs). Returns True iff consistent."""
    keys = sorted({k for r, _ in rows for k in r})
    M = [[Fraction(r.get(k, 0)) for k in keys] + [Fraction(b)] for r, b in rows]
    n = len(keys)
    piv = 0
    for col in range(n):
        p = next((i for i in range(piv, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[piv], M[p] = M[p], M[piv]
        for i in range(len(M)):
            if i != piv and M[i][col] != 0:
                f = M[i][col] / M[piv][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[piv])]
        piv += 1
    return all(any(v != 0 for v in row[:n]) or row[n] == 0 for row in M)


def end_measure(vertices, edges):
    """vertices: {name: order or None (one-ended)}; edges: [(u, v, |G_e|)]."""
    (u0, w0, g0), rest = edges[0], edges[1:]
    vertices = dict(vertices, MID=g0)
    edges = [("MID", u0, g0), ("MID", w0, g0)] + list(rest)
    rows = []
    for i, (u, v, ge) in enumerate(edges):
        rows.append(({f"x{i}+": 1, f"x{i}-": 1, "T": -1}, 0))
    for name, gv in vertices.items():
        if gv is None:
            continue
        r = {"T": Fraction(1)}
        for i, (u, v, ge) in enumerate(edges):
            if u == name:
                r[f"x{i}+"] = r.get(f"x{i}+", 0) - Fraction(gv, ge)
            if v == name:
                r[f"x{i}-"] = r.get(f"x{i}-", 0) - Fraction(gv, ge)
        rows.append((r, gv if name == "MID" else 0))
    return solvable(rows)


def chi(vertices, edges):
    if any(g is None for g in vertices.values()):
        return None
    return sum(Fraction(1, g) for g in vertices.values()) - sum(Fraction(1, e) for *_, e in edges)


EXAMPLES = [
    ("Z (HNN of 1 over 1)", {"v": 1}, [("v", "v", 1)], False),
    ("D_inf = Z/2 * Z/2", {"u": 2, "w": 2}, [("u", "w", 1)], False),
    ("Z x Z/2 (HNN over Z/2)", {"v": 2}, [("v", "v", 2)], False),
    ("F_2", {"v": 1}, [("v", "v", 1), ("v", "v", 1)], True),
    ("PSL2Z = Z/2 * Z/3", {"u": 2, "w": 3}, [("u", "w", 1)], True),
    ("Z/2 * Z/2 * Z/2", {"c": 1, "p": 2, "q": 2, "r": 2}, [("c", "p", 1), ("c", "q", 1), ("c", "r", 1)], True),
    ("Z/4 *_{Z/2} Z/4 (two-ended)", {"u": 4, "w": 4}, [("u", "w", 2)], False),
    ("Z/4 *_{Z/2} Z/6", {"u": 4, "w": 6}, [("u", "w", 2)], True),
    ("Z^2 * Z (HNN of one-ended over 1)", {"v": None}, [("v", "v", 1)], True),
    ("Z^2 * Z/2", {"u": None, "w": 2}, [("u", "w", 1)], True),
    ("Z^2 * Z^2", {"u": None, "w": None}, [("u", "w", 1)], True),
]


def part1():
    ok = True
    for name, V, E, predicted in EXAMPLES:
        s = end_measure(V, E)
        c = chi(V, E)
        pred_rule = (c is None) or (c != 0)
        flag = (s == predicted == pred_rule)
        ok &= flag
        print(f"  {name:38s} solvable={s!s:5s} chi={c!s:6s} predicted={predicted!s:5s} {'OK' if flag else 'MISMATCH'}")
    return ok


# ---------------------------------------------------------------- part 2
def mul(u, v):
    w = list(u)
    for x in v:
        if w and w[-1] == -x:
            w.pop()
        else:
            w.append(x)
    return tuple(w)


def inv(u):
    return tuple(-x for x in reversed(u))


def ball(r, letters=(1, -1, 2, -2)):
    out, frontier = [()], [()]
    for _ in range(r):
        nxt = []
        for w in frontier:
            for x in letters:
                if not w or w[-1] != -x:
                    nxt.append(w + (x,))
        out += nxt
        frontier = nxt
    return out


def subst(images, w):
    out = ()
    for x in w:
        out = mul(out, images[x] if x > 0 else inv(images[-x]))
    return out


# automorphisms given by their inverses' images (we only need phi^-1)
PHI_INV = {
    "id": {1: (1,), 2: (2,)},
    "swap a<->b": {1: (2,), 2: (1,)},
    "a->a^-1": {1: (-1,), 2: (2,)},
    "a->ab (inverse a->aB)": {1: (1, -2), 2: (2,)},
    "a->ab,b->a (inverse a->b,b->Ba)": {1: (2,), 2: (-2, 1)},
}


def part2(R=5, inner=2):
    Bz = ball(R)
    shell = [z for z in Bz if len(z) > inner]
    cs = ball(2)
    pieces = (1, -1, 2, -2)
    indices = {}
    found = 0
    for pname, pinv in PHI_INV.items():
        pz = {z: subst(pinv, z) for z in Bz}
        pc = {c: subst(pinv, inv(c)) for c in cs}
        for combo in product(cs, repeat=4):
            cm = dict(zip(pieces, combo))
            # sigma(y) = phi(y) c_x on U_x, so y = phi^-1(z) phi^-1(c_x^-1), valid iff y ends in x
            def mult(z):
                k = 0
                for x in pieces:
                    y = mul(pz[z], pc[cm[x]])
                    if y and y[-1] == x:
                        k += 1
                return k
            if any(mult(z) != 1 for z in shell):
                continue
            mults = [mult(z) for z in Bz if len(z) <= inner]
            if any(k > 1 for k in mults):
                continue
            uncovered = sum(1 for k in mults if k == 0)
            index = uncovered - 1  # the point e lies outside every piece
            indices[index] = indices.get(index, 0) + 1
            found += 1
    return found, indices


def part2_Z():
    # Z, pieces: positive and negative; sigma(y) = y + c_sign; e = 0 outside pieces
    found = {}
    for cp, cn in product(range(-2, 3), repeat=2):
        R, inner = 40, 5
        def mult(z):
            k = 0
            if z - cp > 0:
                k += 1
            if z - cn < 0:
                k += 1
            return k
        if any(mult(z) != 1 for z in range(-R, R + 1) if abs(z) > inner):
            continue
        m = [mult(z) for z in range(-inner, inner + 1)]
        if any(k > 1 for k in m):
            continue
        idx = sum(1 for k in m if k == 0) - 1
        found[idx] = found.get(idx, 0) + 1
    return found


if __name__ == "__main__":
    print("Part 1: end-measure equations")
    ok1 = part1()
    print("Part 2: F_2 depth-1 twisted piecewise translations")
    n, ind = part2()
    print(f"  near-bijections found: {n}; missed-count (= -index) histogram: {ind}")
    ok2 = n > 0 and set(ind) == {0}
    print("Part 2': Z control")
    indz = part2_Z()
    print(f"  missed-count (= -index) histogram: {indz}")
    ok3 = any(k != 0 for k in indz)
    print("ALL CHECKS PASS" if ok1 and ok2 and ok3 else "CHECK FAILED")
