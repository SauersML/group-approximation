#!/usr/bin/env python3
"""Checks for parallel-repetition-cannot-substitute-rounds-for-alphabet.

1. Elementary inequalities used in the proof (grids).
2. Odd-cycle game (k = 2): explicit feasible basic-SDP solution with deficit
   sin^2(pi/4m), constraint residuals, brute-force opt(G) and opt(G^2) (m = 3),
   and the implied lower bound on the constant C_1 of Steurer's Theorem 1,
   (1 - opt(G^l)) / sqrt(l * eps_ub * ln 2), which must stay bounded in m.
Writes output.txt next to this file and ends with ALL PASS.
"""
import itertools
import math
import os

import numpy as np

OUT = []
FAIL = []


def log(s):
    print(s)
    OUT.append(s)


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        log("FAIL: " + msg)


# ---------- 1. elementary inequalities ----------
def elementary():
    worst = 1.0
    for l in [1, 2, 3, 5, 10, 100, 10**4]:
        for t in np.linspace(1e-6, 0.5, 2001):
            lhs = (1 - t) ** (1.0 / l)
            rhs = 1 - 2 * t / l
            worst = min(worst, lhs - rhs)
            check(lhs >= rhs - 1e-15, f"(1-t)^(1/l) >= 1-2t/l at l={l}, t={t}")
    log(f"[1a] min over grid of (1-t)^(1/l) - (1 - 2t/l) = {worst:.3e} (>= 0)")
    # round budget and lower bound on eta_out
    worst_b, worst_c = 1e9, 1e9
    for l in [1, 2, 3, 7, 50, 1000]:
        for eta in np.geomspace(1e-7, 0.5, 400):
            eo = 1 - (1 - eta) ** l
            if eo > 0.5:
                continue
            worst_b = min(worst_b, 2 * eo - l * eta)
            worst_c = min(worst_c, eo - (1 - 1 / math.e) * l * eta)
            check(l * eta <= 2 * eo + 1e-15, f"l eta <= 2 eta_out at l={l}, eta={eta}")
            check(eo >= (1 - 1 / math.e) * l * eta - 1e-15,
                  f"eta_out >= (1-1/e) l eta at l={l}, eta={eta}")
    log(f"[1b] min 2 eta_out - l eta = {worst_b:.3e}; min eta_out - (1-1/e) l eta = {worst_c:.3e}")
    c_rate = 2 / (1 - 1 / math.e) ** 2
    log(f"[1c] 2/(1-1/e)^2 = {c_rate:.6f} (<= 5.01); x1.5 = {1.5 * c_rate:.6f} (<= 7.51); "
        f"1/sqrt(1-1/e) = {1 / math.sqrt(1 - 1 / math.e):.6f}")
    check(c_rate <= 5.01 and 1.5 * c_rate <= 7.51, "rate constants")
    check(1 / (1 / math.sqrt(1 - 1 / math.e)) >= 0.79, "R2 window constant 0.79")
    check(2 * math.sqrt(math.log(2)) > 1.66, "vacuous threshold C > 1.66 when C_1 >= 1")


# ---------- 2. odd-cycle game ----------
def odd_cycle(m):
    """Constraints (left i, right j, perm as tuple), uniform weights."""
    cons = []
    for i in range(m):
        cons.append((i, i, (0, 1)))            # equality
        cons.append((i, (i + 1) % m, (1, 0)))  # inequality
    return cons


def sdp_solution(m):
    theta = math.pi * (m - 1) / m
    t = math.pi / (2 * m)
    z = np.array([0.0, 0.0, 1.0])

    def vecs(angle):
        x = np.array([math.cos(angle), math.sin(angle), 0.0])
        return [(z + x) / 2, (z - x) / 2]

    U = [vecs(i * theta) for i in range(m)]
    V = [vecs(i * theta + t) for i in range(m)]
    return U, V


def sdp_value(cons, U, V):
    tot = 0.0
    for (i, j, p) in cons:
        tot += sum(float(U[i][a] @ V[j][p[a]]) for a in range(2))
    return tot / len(cons)


def residuals(U):
    r = 0.0
    for u in U:
        r = max(r, abs(float(u[0] @ u[0] + u[1] @ u[1]) - 1), abs(float(u[0] @ u[1])))
    return r


def product(cons, l):
    out = []
    for tup in itertools.product(cons, repeat=l):
        lu = tuple(c[0] for c in tup)
        rv = tuple(c[1] for c in tup)
        perms = tuple(c[2] for c in tup)
        out.append((lu, rv, perms))
    return out


def brute_opt(m, l):
    cons = product(odd_cycle(m), l)
    left = sorted({c[0] for c in cons})
    right = sorted({c[1] for c in cons})
    li = {v: n for n, v in enumerate(left)}
    ri = {v: n for n, v in enumerate(right)}
    K = 2 ** l
    labels = list(itertools.product(range(2), repeat=l))
    lab_idx = {lab: n for n, lab in enumerate(labels)}
    # perm table: for each constraint, map left label index -> right label index
    ptab = np.zeros((len(cons), K), dtype=np.int64)
    for c, (_, _, perms) in enumerate(cons):
        for a, lab in enumerate(labels):
            ptab[c, a] = lab_idx[tuple(perms[s][lab[s]] for s in range(l))]
    cl = np.array([li[c[0]] for c in cons])
    cr = np.array([ri[c[1]] for c in cons])
    nL, nR = len(left), len(right)
    best = 0
    # enumerate left assignments in chunks; best right response per right vertex
    total = K ** nL
    chunk = 4096
    for start in range(0, total, chunk):
        idx = np.arange(start, min(total, start + chunk))
        A = np.zeros((len(idx), nL), dtype=np.int64)
        rem = idx.copy()
        for v in range(nL):
            A[:, v] = rem % K
            rem //= K
        wanted = ptab[np.arange(len(cons))[None, :], A[:, cl]]  # (batch, ncons)
        counts = np.zeros((len(idx), nR, K), dtype=np.int64)
        for c in range(len(cons)):
            np.add.at(counts, (np.arange(len(idx)), cr[c], wanted[:, c]), 1)
        sat = counts.max(axis=2).sum(axis=1)
        best = max(best, int(sat.max()))
    return best / len(cons)


def odd_cycle_checks():
    rows = []
    for m in [3, 5, 7, 9, 11]:
        cons = odd_cycle(m)
        U, V = sdp_solution(m)
        val = sdp_value(cons, U, V)
        res = max(residuals(U), residuals(V))
        eps_ub = 1 - val
        pred = math.sin(math.pi / (4 * m)) ** 2
        check(res < 1e-12, f"SDP constraints m={m}")
        check(abs(eps_ub - pred) < 1e-12, f"SDP deficit = sin^2(pi/4m) at m={m}")
        opt1 = brute_opt(m, 1)
        check(abs(opt1 - (1 - 1 / (2 * m))) < 1e-12, f"opt(G) = 1-1/2m at m={m}")
        rows.append((m, 1, opt1, eps_ub))
        if m == 3:
            opt2 = brute_opt(m, 2)
            check(opt2 >= opt1 ** 2 - 1e-12, "opt(G^2) >= opt(G)^2")
            check(opt2 <= opt1 + 1e-12, "opt(G^2) <= opt(G)")
            rows.append((m, 2, opt2, eps_ub))
    log("[2] odd cycle, k = 2: m, l, opt(G^l), sdp-deficit upper bound eps_ub, "
        "implied C_1 >= (1-opt)/sqrt(l eps_ub ln 2)")
    for (m, l, o, e) in rows:
        c = (1 - o) / math.sqrt(l * e * math.log(2))
        log(f"    m={m:2d} l={l} opt={o:.6f} eps_ub={e:.6f} implied C_1 >= {c:.4f}")
        check(c < 10, f"implied constant bounded at m={m}, l={l}")


if __name__ == "__main__":
    elementary()
    odd_cycle_checks()
    log("ALL PASS" if not FAIL else f"{len(FAIL)} FAILURES")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "output.txt"), "w") as f:
        f.write("\n".join(OUT) + "\n")
