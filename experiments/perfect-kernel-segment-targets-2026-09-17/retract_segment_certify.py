#!/usr/bin/env python3
"""Retract segment steps: research/retract-segment-steps-put-perfect-kernel-one-relator-groups-in-h.md

Adds one rule to experiments/one-relator-hughes-free-char-p-2026-09-17/segment_certify.py
(which itself extends the hierarchy certifier of magnus-hnn-vertex-quotients-2026-09-17).

Rule R (retract hnn step).  G = <a, t | r>, t of exponent sum 0, Magnus rewrite r' in
F(a_0..a_m), m >= 1, A = <a_0..a_{m-1}>.  Suppose the substitution a_m = alpha^-1 s beta^-1
(alpha, beta in F(A)) turns r' into a cyclic word  s^-1 x s y  with x, y in F(A).  Then
S_[0,n+1] is the HNN extension of S_[0,n] along <x_n> -> <y_n^-1> (x_n, y_n: x, y shifted by n).
If for every n some psi in Hom(S_[0,n], Z) takes the value +-1 on x_n or on y_n, then S_[0,n]
retracts onto that cyclic edge group, item 6 of vertex-injective-quotients-give-hughes-free-
division-rings puts S_[0,n+1] in H, and G is in H.  Only ONE edge element has to be seen by Z,
and it has to be seen primitively; rule 1 of segment_certify needs both, rationally.

Hom(S_[0,n], Z) is read through the integral window lattices
    L_0 = Z^m,   L_{n+1} = { (w_1..w_m) : exists w_0 with (w_0..w_{m-1}) in L_n, e.w = 0 },
(the last-m windows of integer solutions of the abelianized relations), and the values of psi
on x_n are  c_x . L_n.  The chain L_0 >= L_1 >= ... is computed exactly (Hermite normal form)
until L_{n+1} = L_n, after which it is constant, so the test "gcd(c_x . L_n) = 1 or
gcd(c_y . L_n) = 1 for every n" is decided exactly.  If the chain has not stabilized after
STAB steps the rule does not fire.

Usage:  retract_segment_certify.py survivors     (the 12 survivors of ../one-relator-hughes-free-char-p-2026-09-17/census-L12.txt + the 8
                                                 length-11 relators left open before rule 1)
        retract_segment_certify.py census L     (full census up to length L)
"""
import os, sys, time
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "one-relator-hughes-free-char-p-2026-09-17"))
import segment_certify as sc  # noqa: E402
hc = sc.hc

STAB = 12

# ---------------------------------------------------------------- integer lattices


def hnf(rows):
    """Row Hermite normal form (integer row operations); returns the nonzero rows."""
    A = [list(r) for r in rows if any(r)]
    if not A:
        return []
    ncol = len(A[0])
    out, r = [], 0
    for c in range(ncol):
        piv = [i for i in range(r, len(A)) if A[i][c] != 0]
        if not piv:
            continue
        while True:
            piv = [i for i in range(r, len(A)) if A[i][c] != 0]
            i0 = min(piv, key=lambda i: abs(A[i][c]))
            A[r], A[i0] = A[i0], A[r]
            done = True
            for i in range(r + 1, len(A)):
                if A[i][c]:
                    q = A[i][c] // A[r][c]
                    A[i] = [a - q * b for a, b in zip(A[i], A[r])]
                    if A[i][c]:
                        done = False
            if done:
                break
        if A[r][c] < 0:
            A[r] = [-a for a in A[r]]
        for i in range(r):
            q = A[i][c] // A[r][c]
            A[i] = [a - q * b for a, b in zip(A[i], A[r])]
        r += 1
        if r == len(A):
            break
    return [row for row in A[:r] if any(row)]


def int_kernel(vals):
    """Basis of {z in Z^k : sum z_i vals_i = 0}."""
    k = len(vals)
    # augmented [vals_i | e_i], HNF on the first column; rows with zero first entry span the kernel
    M = [[vals[i]] + [int(i == j) for j in range(k)] for i in range(k)]
    H = hnf(M)
    ker = [row[1:] for row in H if row[0] == 0]
    return ker


def next_lattice(L, e):
    m = len(e) - 1
    P = [list(b) + [0] for b in L] + [[0] * m + [1]]
    vals = [sum(a * b for a, b in zip(e, v)) for v in P]
    Z = int_kernel(vals)
    vecs = [[sum(z[i] * P[i][j] for i in range(len(P))) for j in range(m + 1)] for z in Z]
    return hnf([v[1:] for v in vecs])


def lattice_chain(e):
    """L_0, L_1, ..., L_N with L_N = L_{N+1}, or None if no stabilization within STAB steps."""
    m = len(e) - 1
    L = [[int(i == j) for j in range(m)] for i in range(m)]
    chain = [L]
    for _ in range(STAB):
        N = next_lattice(L, e)
        if N == L:
            return chain
        chain.append(N)
        L = N
    return None


def values_gcd(L, c):
    g = 0
    for v in L:
        g = gcd(g, sum(a * b for a, b in zip(c, v)))
    return g


# ---------------------------------------------------------------- rule R


def retract_hnn(r, m, maxlen):
    """r: word in letters (0,p), p=0..m.  Rule R from the top; returns a reason or None."""
    e = [0] * (m + 1)
    for (g, p), x in r:
        e[p] += x
    chain = lattice_chain(e)
    if chain is None:
        return None
    A = [(0, p) for p in range(m)]
    top = (0, m)
    cands = hc.short_words(A, maxlen)
    for al in cands:
        for be in cands:
            img = hc.inv(al) + ((sc.SIG, 1),) + hc.inv(be)
            w = hc.cred(hc.subst(r, {top: img}))
            idx = [i for i, (a, _) in enumerate(w) if a == sc.SIG]
            if len(idx) != 2 or w[idx[0]][1] != -w[idx[1]][1]:
                continue
            i, j = idx
            x, y = w[i + 1:j], w[j + 1:] + w[:i]
            if not hc.cred(x) or not hc.cred(y):
                continue
            cx, cy = sc.expvec(x, m), sc.expvec(y, m)
            if all(values_gcd(L, cx) == 1 or values_gcd(L, cy) == 1 for L in chain):
                return "retract-hnn(al=%s,be=%s,stab=%d)" % (sc.show(al), sc.show(be), len(chain) - 1)
    return None


def retract_step_ok(r, lv, maxlen=2):
    if len(lv) != 1:
        return None
    (g, (lo, hi)), = lv.items()
    m = hi - lo
    if m < 1:
        return None
    norm = tuple(((0, p - lo), e) for (gg, p), e in r)
    rev = tuple(((0, m - p), e) for (_, p), e in norm)
    for word, side in ((norm, "top"), (rev, "bottom")):
        why = retract_hnn(word, m, maxlen)
        if why:
            return side + ":" + why
    return None


_prev = hc.root_tower_ok   # = segment_certify.extended_root_tower_ok (landed rules + rule 1)
MODE = {"R": True}
WHY = {}


def with_rule_R(r, lv):
    if _prev(r, lv):
        return True
    if MODE["R"]:
        why = retract_step_ok(r, lv)
        if why:
            WHY[r] = why
            return True
    return False


hc.root_tower_ok = with_rule_R


# ---------------------------------------------------------------- drivers

SURVIVORS12 = """A A B a b a B A A b b
A A B B A A b a B a b
A A A B B a b A b a a B
A A A B a a b b b a a B
A A A B a a b A b a B B
A A A b b a B A B a a b
A A A b a a B B B a a b
A A A b a a B A B a b b
A A B A B A A b a B a b
A A B a B A A b a B a b
A A B a b a B A A b A b
A A B a b a B A A b a b""".split("\n")


def calib():
    """Calibration of the lattice code: e = (0,1,0) gives L_n = {(0,w)} for n >= 1 (H_1 of a
    long segment is Z a_0 + Z a_top); e = (2,-3) (BS(2,3)-type) never stabilizes, L_n = 2^n Z."""
    c1 = lattice_chain([0, 1, 0])
    c2 = lattice_chain([2, -3])
    ok = c1 is not None and c1[-1] == [[0, 1]] and c2 is None
    print("calibration:", "e=(0,1,0) chain", c1, "| e=(2,-3) stabilizes:", c2 is not None,
          "|", "OK" if ok else "FAILED")
    return ok


def survivors():
    ok_all = calib()
    for s in SURVIVORS12 + sc.OPEN11:
        w = hc.parse(s)
        MODE["R"] = False
        sc.MODE["seg"] = True
        ok1, why1 = hc.certify(w, "new", memo={})
        MODE["R"] = True
        WHY.clear()
        ok2, why2 = hc.certify(w, "new", memo={})
        steps = sorted(set(WHY.values()))
        print("%-26s | landed rules + rule 1: %-5s | + rule R: %-5s %s %s"
              % (s, ok1, ok2, why2, steps))
        ok_all &= ok2
    print("ALL CERTIFIED" if ok_all else "SOME UNCERTIFIED")


def census(L):
    gens = [("a", 1), ("a", -1), ("b", 1), ("b", -1)]
    seen, stats, opens = set(), {}, {}
    memo_old, memo_R = {}, {}
    t0 = time.time()

    def words(n):
        def rec(w):
            if len(w) == n:
                if w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]:
                    return
                yield tuple(w)
                return
            for g in gens:
                if w and w[-1][0] == g[0] and w[-1][1] == -g[1]:
                    continue
                w.append(g)
                yield from rec(w)
                w.pop()
        yield from rec([])

    for n in range(2, L + 1):
        for w in words(n):
            if len({a for a, _ in w}) < 2:
                continue
            k = hc.canon(w)
            if k in seen:
                continue
            seen.add(k)
            if hc.is_proper_power(k):
                continue
            MODE["R"] = False
            a, _ = hc.certify(w, "new", memo=memo_old)
            MODE["R"] = True
            b, why = (True, "") if a else hc.certify(w, "new", memo=memo_R)
            stats[(n, a, b)] = stats.get((n, a, b), 0) + 1
            if not b:
                opens.setdefault(n, []).append((k, why))
        print("# length %d done, %.1fs" % (n, time.time() - t0))
        sys.stdout.flush()
    print("length  landed+rule1  +ruleR  count")
    for key in sorted(stats):
        print(*key, stats[key])
    print("uncertified:")
    for n in sorted(opens):
        for k, why in opens[n]:
            print(n, " ".join(("ab"[a] if e == 1 else "AB"[a]) for a, e in k), why)
    print("time %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "census":
        census(int(sys.argv[2]))
    else:
        survivors()
