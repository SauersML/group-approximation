#!/usr/bin/env python3
"""Checks for view-local-branch-selectors-are-gauge-blind.

Part A is exhaustive and covers all selectors at once.
  The window U is k disjoint 3-variable equations on coordinates 0..3k-1.
  Extra variables come after them, and J is a set of extra visible equations.
  Pick random L (dim l, L meet H_U = 0), L' < L of codim 1, x_e in L minus L',
  and a random fixed assignment A. Then enumerate every gauge z in F_2^n.
  The selector sees (b_j + <m_j,z>)_{j in U or J} and tau = (A+z)|L', and it
  must guess (A+z)(x_e). Tabulating the two counts per cell gives the best
  agreement over ALL selectors.
  Claims checked:
    (1) if Q := span(U eqs, J eqs) meets X_U only in H_U (condition F), then
        x_e is not in L' + Q;
    (2) if x_e is not in L' + Q, every cell is balanced, so every selector has
        agreement exactly 1/2;
    (3) control: if x_e is in L' + Q, some selector has agreement 1.

Part B measures the parity leakage of radius-1 views.
  Build random 3LIN with m = c n equations, U = k random equations, and
  J = all equations meeting a window variable. It reports the fraction of
  samples failing F.
"""
import argparse
import random


def rank(vecs):
    basis = {}
    r = 0
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                r += 1
                break
    return r


def in_span(v, vecs):
    return rank(list(vecs) + [v]) == rank(list(vecs))


def dot(a, b):
    return bin(a & b).count("1") & 1


def random_L(k, l, rng, HU):
    nw = 3 * k
    while True:
        L = [rng.getrandbits(nw) for _ in range(l)]
        if rank(L) == l and rank(HU + L) == len(HU) + l:
            return L


def part_a(rng, trials, k, l, extra_vars, extra_eqs):
    nw = 3 * k
    n = nw + extra_vars
    HU = [7 << (3 * i) for i in range(k)]
    W = (1 << nw) - 1
    st = dict(trials=0, F=0, notF=0, viol1=0, viol2=0, balanced=0, leak=0, ctrl_ok=0)
    for _ in range(trials):
        J = [sum(1 << c for c in rng.sample(range(n), 3)) for _ in range(extra_eqs)]
        Q = HU + J
        L = random_L(k, l, rng, HU)
        Lp = L[:-1]
        x = L[-1]
        A = rng.getrandbits(n)
        dimQX = rank(Q) - rank([q & ~W for q in Q])
        F = dimQX == k
        leak = in_span(x, Lp + Q)
        st["trials"] += 1
        st["F" if F else "notF"] += 1
        if F and leak:
            st["viol1"] += 1
        cells = {}
        for z in range(1 << n):
            view = tuple(dot(q, z) for q in Q)
            tau = tuple(dot(y, A ^ z) for y in Lp)
            bit = dot(x, A ^ z)
            cells.setdefault((view, tau), [0, 0])[bit] += 1
        best = sum(max(c) for c in cells.values())
        if not leak:
            if 2 * best != (1 << n):
                st["viol2"] += 1
            else:
                st["balanced"] += 1
        else:
            st["leak"] += 1
            if best == (1 << n):
                st["ctrl_ok"] += 1
    return st


def part_b(rng, n, c, k, samples):
    m = int(c * n)
    eqs = [sum(1 << v for v in rng.sample(range(n), 3)) for _ in range(m)]
    by_var = [[] for _ in range(n)]
    for j, e in enumerate(eqs):
        for i in range(n):
            if e >> i & 1:
                by_var[i].append(j)
    fail = 0
    for _ in range(samples):
        U = rng.sample(range(m), k)
        W = 0
        for j in U:
            W |= eqs[j]
        J = set()
        for i in range(n):
            if W >> i & 1:
                J.update(by_var[i])
        Q = [eqs[j] for j in J]
        dimH = rank([eqs[j] for j in U])
        dimQX = rank(Q) - rank([q & ~W for q in Q])
        if dimQX != dimH:
            fail += 1
    return fail, samples


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260918)
    ap.add_argument("--trials", type=int, default=120)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    bad = 0
    for (k, l, ev, ee) in [(2, 2, 4, 2), (2, 3, 3, 4), (1, 2, 6, 3), (2, 2, 2, 6)]:
        s = part_a(rng, args.trials, k, l, ev, ee)
        print(f"A k={k} l={l} extra_vars={ev} extra_eqs={ee}: {s}")
        bad += s["viol1"] + s["viol2"] + (s["leak"] - s["ctrl_ok"])
    for n in (300, 3000):
        f, t = part_b(rng, n, 2.0, 3, 200)
        print(f"B n={n} m=2n k=3 radius-1 views: F fails on {f}/{t} samples")
    print("PASS" if bad == 0 else f"FAIL ({bad})")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
