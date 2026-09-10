#!/usr/bin/env python3
"""sp-design, task (b) for the lead: the Route-3 descent for the normalisation constant.

THE OBSERVATION THAT MAKES IT CHEAP AND CANONICAL.  Work in the cochain complex of the
n-simplex RELATIVE TO THE VERTEX 0, i.e. cochains vanishing on [0].  It is exact in every
degree (Delta^n is contractible and we killed H^0), and the cone on vertex 0 gives an
explicit contraction h with delta h + h delta = 1:

    h(tau^*) = (tau \\ {0})^*   if 0 is a vertex of tau and tau != [0],   else 0.

At n = 1 this alphabet is exactly the lead's {f, g}: f = [1]^*, g = delta f = [01]^*.

Then for the p-fold tensor power, H := h (x) 1 (x) ... (x) 1 (apply h to slot 0 only)
satisfies D H + H D = 1 ON THE NOSE.  Proof: the two mixed terms of the Koszul-signed
tensor differential cancel because h lowers degree by one, so
epsilon(h a) = - h(epsilon a).  Verified numerically below.

So every primitive in the descent is Y = H(A) with no linear solve, PROVIDED D A = 0 --
which holds at every level because N (T - 1) = (T - 1) N = T^p - 1 = 0, so
D A_{k+1} = D op(Y_k) = op(D Y_k) = op(A_k) = op(op'(Y_{k-1})) = 0.
That makes p = 13 (and far beyond) instant, and it makes the coefficient vectors CANONICAL,
which is what a closed form in p has to be recognised from.

DESCENT.  A_0 = (delta u_0)^{(x)p} at W-index q(p-1); at each level Y = H(A),
A := op(Y) with op = N when the W-index is even and (T-1) when it is odd; W-index -= 1.
For p odd and q = 1 the starting index p-1 is even, so the first operator is N.
c_q = < A_final, iterated Alexander-Whitney diagonal of the fundamental simplex >.
"""
import sys
from itertools import product, combinations


# ---------------------------------------------------------------- the relative complex

class RelSimplexCochains:
    """C^*(Delta^n, {0}): basis = faces tau of [0..n] with tau != [0], as duals.
    Degree of tau^* = |tau| - 1."""

    def __init__(self, n):
        self.n = n
        faces = []
        for k in range(1, n + 2):
            for c in combinations(range(n + 1), k):
                faces.append(c)
        self.basis = [t for t in faces if t != (0,)]
        self.deg = {t: len(t) - 1 for t in self.basis}
        self.delta = {}
        for t in self.basis:
            img = {}
            # <delta tau^*, sigma> = <tau^*, d sigma>: sigma ranges over (deg+1)-faces
            for s in self.basis:
                if len(s) != len(t) + 1:
                    continue
                for i in range(len(s)):
                    if s[:i] + s[i + 1:] == t:
                        img[s] = img.get(s, 0) + (-1) ** i
            self.delta[t] = {k: v for k, v in img.items() if v}

    def h(self, t):
        """the cone contraction, dual to sigma |-> [0, sigma]."""
        if t[0] == 0 and len(t) >= 2:
            return t[1:]
        return None


# ---------------------------------------------------------------- words and operators

def wdeg(C, w):
    return sum(C.deg[l] for l in w)


def Dop(C, vec, p):
    out = {}
    for w, c in vec.items():
        if not c % p:
            continue
        pre = 0
        for j, l in enumerate(w):
            for l2, c2 in C.delta[l].items():
                w2 = w[:j] + (l2,) + w[j + 1:]
                out[w2] = (out.get(w2, 0) + ((-1) ** pre) * c2 * c) % p
            pre += C.deg[l]
    return {k: v for k, v in out.items() if v % p}


def Hop(C, vec, p):
    out = {}
    for w, c in vec.items():
        l = C.h(w[0])
        if l is None:
            continue
        w2 = (l,) + w[1:]
        out[w2] = (out.get(w2, 0) + c) % p
    return {k: v for k, v in out.items() if v % p}


def Top(C, vec, p):
    out = {}
    for w, c in vec.items():
        d0 = C.deg[w[0]]
        s = (-1) ** (d0 * (wdeg(C, w) - d0))
        w2 = w[1:] + (w[0],)
        out[w2] = (out.get(w2, 0) + s * c) % p
    return {k: v for k, v in out.items() if v % p}


def Nop(C, vec, p):
    out = {}
    cur = dict(vec)
    for _ in range(p):
        for k, v in cur.items():
            out[k] = (out.get(k, 0) + v) % p
        cur = Top(C, cur, p)
    return {k: v for k, v in out.items() if v % p}


def TminusOne(C, vec, p):
    out = dict(Top(C, vec, p))
    for k, v in vec.items():
        out[k] = (out.get(k, 0) - v) % p
    return {k: v for k, v in out.items() if v % p}


def addv(a, b, p, s=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = (out.get(k, 0) + s * v) % p
    return {k: v for k, v in out.items() if v % p}


# ---------------------------------------------------------------- AW pairing

def aw_terms(n, p):
    """iterated AW diagonal of [0..n]: p-tuples of faces
    ([0..i1],[i1..i2],...,[i_{p-1}..n])."""
    out = []
    for cuts in product(range(n + 1), repeat=p - 1):
        if any(cuts[i] > cuts[i + 1] for i in range(len(cuts) - 1)):
            continue
        idx = (0,) + cuts + (n,)
        faces = tuple(tuple(range(idx[j], idx[j + 1] + 1)) for j in range(p))
        out.append(faces)
    return out


def pair_with_aw(C, vec, n, p):
    """< vec, AW^{(p)}([0..n]) > with the Koszul sign (-1)^{sum_{i<j} |l_i||l_j|}."""
    terms = aw_terms(n, p)
    tot = 0
    for w, c in vec.items():
        degs = [C.deg[l] for l in w]
        sign = (-1) ** sum(degs[i] * degs[j] for i in range(p) for j in range(i + 1, p))
        for faces in terms:
            ok = True
            for l, fc in zip(w, faces):
                if l != fc:
                    ok = False
                    break
            if ok:
                tot += sign * c
    return tot % p


# ---------------------------------------------------------------- the descent

def descent(p, n, u0, verbose=True):
    """u0: the degree-(n-1) basis cochain whose coboundary starts the descent
    (n = 1: u0 = (1,), delta u0 = (0,1);  n = 2: u0 = (1,2), delta u0 = (0,1,2))."""
    C = RelSimplexCochains(n)
    q = n
    du0 = C.delta[u0]
    assert len(du0) == 1, ("delta u0 is not a single basis element", du0)
    (top, ctop), = du0.items()
    A = {(top,) * p: pow(ctop, p, p) % p}
    Widx = q * (p - 1)
    levels = []
    while Widx > 0:
        assert not Dop(C, A, p), f"A is not a D-cocycle at W-index {Widx}"
        Y = Hop(C, A, p)
        chk = Dop(C, Y, p)
        if addv(chk, A, p, -1):
            return dict(status=f"H FAILED to be a primitive at W-index {Widx}")
        op, opname = (Nop, "N") if Widx % 2 == 0 else (TminusOne, "(T-1)")
        A = op(C, Y, p)
        levels.append(dict(Widx=Widx, op=opname, nY=len(Y), Y=Y, nA=len(A)))
        Widx -= 1
    c = pair_with_aw(C, A, n, p)
    return dict(status="OK", c=c, levels=levels, final=A)


def norm_sign_vector(p):
    C = RelSimplexCochains(1)
    f, g = (1,), (0, 1)
    v0 = {(f,) + (g,) * (p - 1): 1}
    eps = []
    cur = dict(v0)
    for k in range(p):
        (w, c), = cur.items()
        eps.append((k, w.index(f), c % p))
        cur = Top(C, cur, p)
    Nv = Nop(C, v0, p)
    coeffs = [Nv.get((g,) * j + (f,) + (g,) * (p - 1 - j), 0) % p for j in range(p)]
    return eps, coeffs


def sym(c, p):
    return c if c <= p // 2 else c - p


def show_word(C, w):
    return "".join(str(C.deg[l]) for l in w)


if __name__ == "__main__":
    primes = [3, 5, 7, 11, 13]
    do2 = True
    if len(sys.argv) > 1:
        primes = [int(a) for a in sys.argv[1:] if a.isdigit()]
        do2 = "no2" not in sys.argv
    C1 = RelSimplexCochains(1)
    f, g = (1,), (0, 1)

    print("### sanity: D H + H D = 1 on the p-fold tensor power", flush=True)
    for p in [3, 5]:
        C = RelSimplexCochains(1)
        bad = 0
        for w in product(C.basis, repeat=p):
            v = {w: 1}
            lhs = addv(Dop(C, Hop(C, v, p), p), Hop(C, Dop(C, v, p), p), p)
            if addv(lhs, v, p, -1):
                bad += 1
        print(f"  p={p}, n=1: words failing D H + H D = 1: {bad}", flush=True)

    print()
    print("### c_1: the descent on Delta^1", flush=True)
    for p in primes:
        eps, coeffs = norm_sign_vector(p)
        res = descent(p, 1, f)
        print("=" * 70, flush=True)
        print(f"p = {p}", flush=True)
        print("  N on (one degree-0 slot, p-1 degree-1 slots):", flush=True)
        print("    T^k v_0 = eps_k v_m :  "
              + ", ".join(f"(k={k}, m={m}, {sym(e,p):+d})" for k, m, e in eps), flush=True)
        print(f"    coefficients of N v_0 on v_j (j = 0..p-1): "
              f"{[sym(c,p) for c in coeffs]}", flush=True)
        print("    equals (-1)^j for every j: "
              + str(all((coeffs[j] - (1 if j % 2 == 0 else p - 1)) % p == 0
                        for j in range(p))), flush=True)
        if res["status"] != "OK":
            print("  DESCENT:", res["status"], flush=True)
            continue
        print(f"  c_1 = {sym(res['c'], p)}   ({'NONZERO' if res['c'] % p else 'ZERO'} mod {p})",
              flush=True)
        for lv in res["levels"]:
            Y = lv["Y"]
            desc = ", ".join(f"{show_word(C1, w)}:{sym(c,p):+d}"
                             for w, c in sorted(Y.items()))
            head = (f"    W-index {lv['Widx']:3d}  op {lv['op']:6s}  |Y| = {lv['nY']:5d}"
                    f"  |A_next| = {lv['nA']:5d}")
            print(head + ("   Y = " + desc if len(desc) < 300 else ""), flush=True)

    if do2:
        print()
        print("### c_2: the descent on Delta^2 (u = delta g, g = [12]^*)", flush=True)
        for p in primes:
            if p > 7:
                print(f"  p = {p}: skipped (6^p words)", flush=True)
                continue
            res = descent(p, 2, (1, 2))
            if res["status"] != "OK":
                print(f"  p = {p}: {res['status']}", flush=True)
                continue
            print(f"  p = {p}: c_2 = {sym(res['c'], p)}  "
                  f"({'NONZERO' if res['c'] % p else 'ZERO'} mod {p});  levels "
                  f"{[ (lv['Widx'], lv['op'], lv['nY']) for lv in res['levels'] ][:6]}"
                  f"{'...' if len(res['levels'])>6 else ''}", flush=True)
