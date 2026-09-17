#!/usr/bin/env python3
"""Machine check of the rotation-pointer gadget firewall: (L), (R) and (Q) do not force domination.

Target node: quadrangle-closed-patterns-do-not-force-domination
Artifact:    research/artifacts/quadrangle-closed-pattern-firewall-2026-09-17.md

Pattern (q = 2, k = 2^t, R gadgets, L prime pointer positions, n prime value positions, m = (n-1)/2):
  columns: u_0..u_{L-1} (pointers), v_0..v_{n-1} (values)
  gadget rho, shift a = a_rho, step c = c_rho, isolated point z = z_rho, s_i = z+(2i-1)c, t_i = z+2ic (mod n)
  rows W_0, W_1, W_2 with  W_i u_y = p(rho, y + i a mod L)
  W_0: s_i -> A_i,  t_i -> C_i (i<m), t_m -> D,  z -> Ep
  W_1: s_i -> B_i,  t_i -> A_i,                  z -> o
  W_2: t_i -> B_i,  s_{i+1} -> C_i (i<m),  z -> D,  s_1 -> Ep
Code: psi = (j, XOR_{e in values} x(e)[j]), j = sum of the low t bits of the L pointer inputs mod k.

Sections:
  1. Build; check full rectangle, (L), (R), value multiplicities (only o odd), pointer-set invariance.
  2. (Q) through row-pair classes (disjoint-or-equal), plus brute-force (Q) on a small instance
     and a negative control (all gadgets with one shift) that must fail (Q).
  3. No coherent cyclic 3-shift, |Delta| mod 3 not 0 (outside the mod-3 invariant).
  4. Holonomy: a word in the classes fixes s_1 but moves every pointer, so no group realizes it.
  5. Phi bound and Monte Carlo decoding of x(o)[j_rho] from y_F.
Deterministic seeds. Writes verify_rotation_gadget.json next to this file.
"""
import itertools
import json
import math
import os
import random

import numpy as np

OUT = {}


def is_prime(p):
    if p < 2:
        return False
    for d in range(2, int(p ** 0.5) + 1):
        if p % d == 0:
            return False
    return True


def next_prime(p, cond=lambda p: True):
    while not (is_prime(p) and cond(p)):
        p += 1
    return p


def choose_shifts(R, L):
    """Greedy shifts a with {a,-a,2a,-2a} of size 4 and pairwise disjoint across gadgets."""
    used, shifts = set(), []
    for a in range(1, L):
        S = {a % L, (-a) % L, (2 * a) % L, (-2 * a) % L}
        if len(S) == 4 and 0 not in S and not (S & used):
            shifts.append(a)
            used |= S
            if len(shifts) == R:
                return shifts
    return None


# ---------------------------------------------------------------- 1. the pattern

def params(k, R=None, L=None, n=None):
    t = int(round(math.log2(k)))
    assert 2 ** t == k
    if R is None:
        R = math.ceil(2 * k * math.log(k))
    if n is None:
        n = next_prime(R * R + R + 1)
    m = (n - 1) // 2
    if L is None:
        L = 4 * R + 1
        while True:
            L = next_prime(L, lambda p: p % 3 == 1 and (3 * m + 2) % p != 0)
            if choose_shifts(R, L) is not None:
                break
            L += 1
    shifts = choose_shifts(R, L)
    assert shifts is not None
    return dict(k=k, t=t, R=R, L=L, n=n, m=m, shifts=shifts)


def build(P, shifts=None):
    R, L, n, m = P["R"], P["L"], P["n"], P["m"]
    shifts = P["shifts"] if shifts is None else shifts
    cols = [("u", y) for y in range(L)] + [("v", x) for x in range(n)]
    rows, w = [], {}
    for rho in range(R):
        a, c, z = shifts[rho], rho + 1, (rho * (R + 1)) % n
        s = lambda i: ("v", (z + (2 * i - 1) * c) % n)
        tt = lambda i: ("v", (z + 2 * i * c) % n)
        W = [("W", rho, i) for i in range(3)]
        rows += W
        for i in range(3):
            for y in range(L):
                w[(W[i], ("u", y))] = ("p", rho, (y + i * a) % L)
        for i in range(1, m + 1):
            w[(W[0], s(i))] = ("A", rho, i)
            w[(W[1], tt(i))] = ("A", rho, i)
            w[(W[1], s(i))] = ("B", rho, i)
            w[(W[2], tt(i))] = ("B", rho, i)
            if i < m:
                w[(W[0], tt(i))] = ("C", rho, i)
                w[(W[2], s(i + 1))] = ("C", rho, i)
        w[(W[0], tt(m))] = ("D", rho)
        w[(W[2], ("v", z))] = ("D", rho)
        w[(W[0], ("v", z))] = ("Ep", rho)
        w[(W[2], s(1))] = ("Ep", rho)
        w[(W[1], ("v", z))] = "o"
    return rows, cols, w


def check_basic(P, rows, cols, w):
    res = {}
    res["full_rectangle"] = all((r, c) in w for r in rows for c in cols) and len(w) == len(rows) * len(cols)
    res["L_rows_injective"] = all(len({w[(r, c)] for c in cols}) == len(cols) for r in rows)
    res["R_cols_injective"] = all(len({w[(r, c)] for r in rows}) == len(rows) for c in cols)
    ok_mult, ok_ptr = True, True
    for rho in range(P["R"]):
        W = [("W", rho, i) for i in range(3)]
        cnt = {}
        for r in W:
            for c in cols:
                if c[0] == "v":
                    cnt[w[(r, c)]] = cnt.get(w[(r, c)], 0) + 1
        odd = [s for s, v in cnt.items() if v % 2 == 1]
        ok_mult &= (odd == ["o"]) and all(v in (1, 2) for v in cnt.values())
        ptr = [frozenset(w[(r, c)] for c in cols if c[0] == "u") for r in W]
        ok_ptr &= ptr[0] == ptr[1] == ptr[2]
        vals = set(cnt)
        ok_ptr &= not (vals & set(ptr[0]))
    res["value_xor_is_o"] = ok_mult
    res["pointer_sets_equal_and_disjoint_from_values"] = ok_ptr
    return res


# ---------------------------------------------------------------- 2. quadrangle closure

def classes(rows, cols, w):
    """R(c,c') = {(e,e') : c e = c' e'} for ordered pairs of distinct rows (nonempty ones only)."""
    readers = {}
    for (r, c), s in w.items():
        readers.setdefault(s, []).append((r, c))
    cls = {}
    for s, lst in readers.items():
        for (r, c), (r2, c2) in itertools.permutations(lst, 2):
            cls.setdefault((r, r2), set()).add((c, c2))
    return cls


def check_Q_classes(cls):
    """(Q) holds iff any two classes are disjoint or equal (given (L), (R))."""
    owner = {}
    bad = 0
    for rp, S in cls.items():
        fs = frozenset(S)
        for pair in S:
            if pair in owner and owner[pair] != fs:
                bad += 1
            owner.setdefault(pair, fs)
    distinct = len({frozenset(S) for S in cls.values()})
    return bad == 0, bad, distinct


def check_Q_bruteforce(rows, cols, w):
    """Literal (Q): c e = c' e', c r = c' r', d e = d' e'  ==>  d r = d' r', over all rows incl. c = c'."""
    rowpairs_of = {}
    pairs_of = {}
    for c, c2 in itertools.product(rows, rows):
        S = {(e, e2) for e in cols for e2 in cols if w[(c, e)] == w[(c2, e2)]}
        pairs_of[(c, c2)] = S
        for p in S:
            rowpairs_of.setdefault(p, set()).add((c, c2))
    violations = 0
    checked = 0
    for (c, c2), S in pairs_of.items():
        for (e, e2) in S:
            for (d, d2) in rowpairs_of[(e, e2)]:
                T = pairs_of[(d, d2)]
                for (r, r2) in S:
                    checked += 1
                    if (r, r2) not in T:
                        violations += 1
    return violations, checked


# ---------------------------------------------------------------- 3. coherent 3-shifts and |Delta|

def coherent_shift_triples(rows, cls):
    count = 0
    for W1, W2, W3 in itertools.permutations(rows, 3):
        A = cls.get((W1, W2))
        B = cls.get((W2, W3))
        C = cls.get((W3, W1))
        if A and B and C and (A & B & C):
            count += 1
    return count


def delta_sizes(P, cols, w):
    out = set()
    for rho in range(P["R"]):
        sets = [{w[(("W", rho, i), c)] for c in cols} for i in range(3)]
        out.add(len(sets[0] ^ sets[1] ^ sets[2]))
    return sorted(out)


# ---------------------------------------------------------------- 4. holonomy (no group realizes it)

def holonomy(P, cls):
    m, L = P["m"], P["L"]
    W = [("W", 0, i) for i in range(3)]
    tau = dict(cls[(W[0], W[1])])
    tau2 = dict(cls[(W[1], W[2])])
    sigma = dict(cls[(W[0], W[2])])
    word = ["tau", "sigma"] * m + ["sigma"]  # applied left to right, starting at s_1
    maps = {"tau": tau, "sigma": sigma}
    s1 = ("v", 1 % P["n"])  # gadget 0: z = 0, c = 1
    x = s1
    trace_ok = True
    for g in word:
        if x not in maps[g]:
            trace_ok = False
            break
        x = maps[g][x]
    fixes_s1 = trace_ok and x == s1
    moved, in_domain = 0, 0
    for y in range(L):
        x = ("u", y)
        ok = True
        for g in word:
            if x not in maps[g]:
                ok = False
                break
            x = maps[g][x]
        if ok:
            in_domain += 1
            moved += x != ("u", y)
    return dict(tau_equals_R_W1_W2=tau == tau2, word_length=len(word), word_fixes_s1=fixes_s1,
                pointers_in_domain=in_domain, pointers_moved=moved,
                pointer_displacement=(-(3 * m + 2) * P["shifts"][0]) % L,
                gcd_L_3m_plus_2=math.gcd(L, 3 * m + 2))


# ---------------------------------------------------------------- 5. Phi bound and decoding

def phi_bound(P):
    k, t, R = P["k"], P["t"], P["R"]
    resid = k * (1 - 1 / k) ** R
    return dict(H_psi_bits=t + 1, residual_bound_bits=resid, Phi_upper=(t + 1 + resid) / k)


def monte_carlo(P, rows, cols, w, trials, seed):
    k, t, R = P["k"], P["t"], P["R"]
    sites = sorted({s for s in w.values()}, key=repr)
    idx = {s: i for i, s in enumerate(sites)}
    ptr_cols = [c for c in cols if c[0] == "u"]
    val_cols = [c for c in cols if c[0] == "v"]
    PI = np.array([[idx[w[(r, c)]] for c in ptr_cols] for r in rows])
    VI = np.array([[idx[w[(r, c)]] for c in val_cols] for r in rows])
    o = idx["o"]
    rng = np.random.default_rng(seed)
    weights = (1 << np.arange(t)).astype(np.int64)
    errors, uncovered_total, j_mismatch = 0, 0, 0
    for _ in range(trials):
        X = rng.integers(0, 2, size=(len(sites), k), dtype=np.int64)
        low = X[:, :t] @ weights  # low t bits as integers
        J = low[PI].sum(axis=1) % k  # one j per row
        bits = X[VI, J[:, None]].sum(axis=1) % 2  # XOR of value bits at j
        covered = set()
        for rho in range(R):
            rr = [3 * rho, 3 * rho + 1, 3 * rho + 2]
            if not (J[rr[0]] == J[rr[1]] == J[rr[2]]):
                j_mismatch += 1
                continue
            j = int(J[rr[0]])
            guess = int(bits[rr].sum() % 2)
            errors += guess != int(X[o, j])
            covered.add(j)
        uncovered_total += k - len(covered)
    return dict(trials=trials, decoding_errors=errors, j_mismatches=j_mismatch,
                mean_uncovered=uncovered_total / trials, expected_uncovered=k * (1 - 1 / k) ** R)


# ---------------------------------------------------------------- main

def main():
    random.seed(0)
    # small instance: brute-force (Q), negative control
    Ps = params(2, R=3)
    rows, cols, w = build(Ps)
    small = dict(params={kk: Ps[kk] for kk in ("k", "R", "L", "n", "m", "shifts")})
    small["basic"] = check_basic(Ps, rows, cols, w)
    small["Q_classes"] = check_Q_classes(classes(rows, cols, w))[:2]
    v, chk = check_Q_bruteforce(rows, cols, w)
    small["Q_bruteforce"] = dict(violations=v, instances_checked=chk)
    small["coherent_3shift_triples"] = coherent_shift_triples(rows, classes(rows, cols, w))
    small["delta_sizes"] = delta_sizes(Ps, cols, w)
    small["holonomy"] = holonomy(Ps, classes(rows, cols, w))
    rows_b, cols_b, w_b = build(Ps, shifts=[Ps["shifts"][0]] * Ps["R"])
    vb, chkb = check_Q_bruteforce(rows_b, cols_b, w_b)
    small["negative_control_one_shift"] = dict(basic=check_basic(Ps, rows_b, cols_b, w_b),
                                               Q_violations=vb, instances_checked=chkb)
    OUT["small_k2_R3"] = small
    print("small", json.dumps(small, default=str))

    for k, trials in ((4, 3000), (8, 300)):
        P = params(k)
        rows, cols, w = build(P)
        cls = classes(rows, cols, w)
        rep = dict(params={kk: P[kk] for kk in ("k", "t", "R", "L", "n", "m")},
                   shifts=P["shifts"])
        rep["basic"] = check_basic(P, rows, cols, w)
        okQ, bad, distinct = check_Q_classes(cls)
        rep["Q_classes"] = dict(holds=okQ, bad_memberships=bad, distinct_nonempty_classes=distinct)
        if k == 4:
            rep["coherent_3shift_triples"] = coherent_shift_triples(rows, cls)
        rep["delta_sizes"] = delta_sizes(P, cols, w)
        rep["holonomy"] = holonomy(P, cls)
        rep["phi"] = phi_bound(P)
        rep["monte_carlo"] = monte_carlo(P, rows, cols, w, trials, seed=k)
        OUT[f"k{k}"] = rep
        print(f"k={k}", json.dumps(rep, default=str))

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "verify_rotation_gadget.json"), "w") as fh:
        json.dump(OUT, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
