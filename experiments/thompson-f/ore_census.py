#!/usr/bin/env python3
"""Exact F_2 census for Guba's open Ore problems in the positive monoid M of Thompson's group F.

M = < x_0, x_1, ... | x_j x_i = x_i x_{j+1} (i < j) >, normal forms x_{i1} ... x_{is}, i1 <= ... <= is.

Modes
  p22   : for every pair (a, b) of nonzero elements of F_2[S_{3,5}] (the 9 degree-2 monomials
          x_i x_j, i <= j, i <= 2, j <= 3), decide whether a u = b v has a nonzero homogeneous
          solution with deg u = deg v = D and all letters <= L (Guba, survey arXiv:2305.07113, Problem P_{2,2}).
  forms : for a set of linear forms l = alpha x0 + beta x1 + gamma x2 over F_2, compute
          dim of  cap_l  l * F_2[M_{D,L}]  inside F_2[M_{D+1}] (common right multiples; Problem Q_k).

Everything is exact linear algebra over F_2 with Python ints as bit rows.
"""
import itertools, sys, json, time

def left_mul_letter(j, word):
    """Normal form of x_j * word, word a nondecreasing tuple."""
    out = []
    k = 0
    n = len(word)
    while k < n and word[k] < j:
        out.append(word[k]); j += 1; k += 1
    out.append(j)
    out.extend(word[k:])
    return tuple(out)

def mul(w1, w2):
    """Normal form of w1 * w2 (both normal forms)."""
    r = w2
    for j in reversed(w1):
        r = left_mul_letter(j, r)
    return r

def monomials(deg, L, lo=0):
    return [c for c in itertools.combinations_with_replacement(range(lo, L + 1), deg)]

def rank_f2(rows):
    """Rank of a list of ints (bit vectors) over F_2."""
    piv = {}
    r = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v; r += 1
                break
    return r

def selftest():
    # defining relations x_j x_i = x_i x_{j+1}
    for i in range(4):
        for j in range(i + 1, 5):
            assert mul((j,), (i,)) == (i, j + 1), (i, j)
    # associativity on random words
    import random
    random.seed(1)
    for _ in range(2000):
        ws = [tuple(sorted(random.randrange(5) for _ in range(random.randrange(4)))) for _ in range(3)]
        assert mul(mul(ws[0], ws[1]), ws[2]) == mul(ws[0], mul(ws[1], ws[2]))
    return True

def image_columns(elem, basis, index):
    """For elem = list of monomials (F_2 sum), return for each basis monomial u the bitmask of elem*u."""
    cols = []
    for u in basis:
        mask = 0
        for s in elem:
            p = mul(s, u)
            k = index.setdefault(p, len(index))
            mask ^= (1 << k)
        cols.append(mask)
    return cols

def pair_solvable(a, b, basis):
    index = {}
    ca = image_columns(a, basis, index)
    cb = image_columns(b, basis, index)
    # nonzero kernel of (u,v) -> a u + b v  (over F_2, minus = plus)  iff rank < 2|basis|
    return rank_f2(ca + cb) < 2 * len(basis)

def p22(D, L, limit=None):
    S = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3)]
    elems = []
    for mask in range(1, 1 << 9):
        elems.append([S[i] for i in range(9) if mask >> i & 1])
    basis = monomials(D, L)
    unsolved = []
    count = 0
    t0 = time.time()
    for ia in range(len(elems)):
        for ib in range(ia + 1, len(elems)):
            if limit and count >= limit:
                break
            count += 1
            if not pair_solvable(elems[ia], elems[ib], basis):
                unsolved.append((ia + 1, ib + 1))
    return {"mode": "p22", "D": D, "L": L, "basis": len(basis), "pairs_tested": count,
            "unsolved": len(unsolved), "unsolved_masks_first50": unsolved[:50], "seconds": round(time.time() - t0, 1)}

def forms_intersection(forms, D, L):
    """dim of cap_l l*F_2[M_{D,L}], forms given as masks over (x0,x1,x2)."""
    basis = monomials(D, L)
    index = {}
    spans = []
    for f in forms:
        elem = [(i,) for i in range(3) if f >> i & 1]
        spans.append(image_columns(elem, basis, index))
    # dim of intersection of subspaces W_1..W_m: iterate  dim(W cap W') = dim W + dim W' - dim(W + W')
    # computed exactly by Zassenhaus-style elimination on the current intersection basis.
    cur = spans[0]
    for W in spans[1:]:
        cur = intersect(cur, W)
        if not cur:
            return 0
    return rank_f2(cur)

def intersect(U, W):
    """Basis of U cap W over F_2 (U, W lists of ints) via kernel of [U | W]."""
    nU = len(U)
    # rows v = (vector, combination-mask over U and W generators)
    piv = {}
    kernel = []
    for idx, vec in enumerate(U + W):
        comb = 1 << idx
        v = vec
        while v:
            h = v.bit_length() - 1
            if h in piv:
                pv, pc = piv[h]; v ^= pv; comb ^= pc
            else:
                piv[h] = (v, comb); break
        if v == 0:
            kernel.append(comb)
    out = []
    for comb in kernel:
        s = 0
        for i in range(nU):
            if comb >> i & 1:
                s ^= U[i]
        if s:
            out.append(s)
    return out

if __name__ == "__main__":
    assert selftest()
    mode = sys.argv[1]
    if mode == "p22":
        D, L = int(sys.argv[2]), int(sys.argv[3])
        lim = int(sys.argv[4]) if len(sys.argv) > 4 else None
        print(json.dumps(p22(D, L, lim)))
    elif mode == "forms":
        D, L = int(sys.argv[2]), int(sys.argv[3])
        forms = [int(x) for x in sys.argv[4].split(",")]
        print(json.dumps({"mode": "forms", "D": D, "L": L, "forms": forms, "dim": forms_intersection(forms, D, L)}))
