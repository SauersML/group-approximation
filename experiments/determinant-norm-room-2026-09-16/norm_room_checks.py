#!/usr/bin/env python3
"""Numerical sanity checks for research/artifacts/determinant-norm-room-2026-09-16.md.

1. Tripod norms rho(T_{k,k,k}) increase to 3/sqrt(2); Rayleigh lower bound R_k.
2. Hub-cycle cubic port operators B over finite groups H and their
   L-subdivisions A_L:
   - every port has degree 3, internal vertices degree 2, graph connected;
   - rho(T_{L-1,L-1,L-1}) <= ||A_L|| <= 3/sqrt(2) + 3 * 2^{-(L+1)/2};
   - Schur test vector f satisfies A_L f <= (3/sqrt2 + 3*2^{-(L+1)/2}) f;
   - spectrum identity: eig(A_L) = {2cos(pi j/L), mult (k/2)|H|} union
     {x : p_L(x) = t, t in eig(B)}, p_L(x) = U_L(x/2) - 2 U_{L-2}(x/2).
Single-threaded, small matrices (at most a few thousand rows).
"""
import itertools
import math
import sys

import numpy as np

LAM = 3 / math.sqrt(2)


def path_adj(edges, nv):
    M = np.zeros((nv, nv))
    for u, v in edges:
        M[u, v] += 1
        M[v, u] += 1
    return M


def tripod(k):
    edges = []
    nv = 1 + 3 * k
    for leg in range(3):
        prev = 0
        for j in range(1, k + 1):
            v = 1 + leg * k + (j - 1)
            edges.append((prev, v))
            prev = v
    return path_adj(edges, nv)


def rho(M):
    return float(np.max(np.abs(np.linalg.eigvalsh(M))))


def rayleigh_lower(k):
    return 6 * 2 ** -0.5 * (2 - 2 ** (1 - k)) / (4 - 3 * 2 ** -k)


def cheb_U_polys(L):
    """Return list of numpy poly1d U_k(x/2) for k = 0..L."""
    U = [np.poly1d([1.0]), np.poly1d([1.0, 0.0])]
    for k in range(1, L):
        U.append(np.poly1d([1.0, 0.0]) * U[k] - U[k - 1])
    return U


def p_L(L):
    U = cheb_U_polys(L)
    return U[L] - 2 * U[L - 2]


def group_cyclic(m):
    elems = list(range(m))
    mul = lambda a, b: (a + b) % m
    return elems, mul


def group_s3():
    elems = list(itertools.permutations(range(3)))
    mul = lambda a, b: tuple(a[b[i]] for i in range(3))
    return elems, mul


def group_dihedral(m):
    # elements (r, s): x -> s*x + r on Z/m with s in {1,-1}
    elems = [(r, s) for r in range(m) for s in (1, -1)]
    mul = lambda a, b: ((a[0] + a[1] * b[0]) % m, a[1] * b[1])
    return elems, mul


def port_edges(elems, mul, gens):
    """Hub-cycle cubic port graph: types P_0..P_{2d-1} per h.
    Hub cycle P_0-P_1-...-P_{2d-1}-P_0 at each h, external edge
    (h, P_{2i}) - (h s_i, P_{2i+1})."""
    d = len(gens)
    idx = {h: i for i, h in enumerate(elems)}
    k = 2 * d
    vid = lambda h, p: idx[h] * k + p
    edges = []
    for h in elems:
        for p in range(k):
            edges.append((vid(h, p), vid(h, (p + 1) % k)))
        for i, s in enumerate(gens):
            edges.append((vid(h, 2 * i), vid(mul(h, s), 2 * i + 1)))
    return edges, len(elems) * k, k


def subdivide(edges, nv, L):
    new_edges = []
    nxt = nv
    for u, v in edges:
        chain = [u] + list(range(nxt, nxt + L - 1)) + [v]
        nxt += L - 1
        for a, b in zip(chain, chain[1:]):
            new_edges.append((a, b))
    return new_edges, nxt


def connected(M):
    n = M.shape[0]
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in np.nonzero(M[u])[0]:
            v = int(v)
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n


def check_case(name, elems, mul, gens, L, report):
    edges, nvB, k = port_edges(elems, mul, gens)
    B = path_adj(edges, nvB)
    assert np.all(B.sum(axis=1) == 3), "ports must be cubic"
    sedges, nvA = subdivide(edges, nvB, L)
    A = path_adj(sedges, nvA)
    deg = A.sum(axis=1)
    assert np.all(deg[:nvB] == 3) and np.all(deg[nvB:] == 2)
    conn = connected(A)
    normA = rho(A)
    upper = LAM + 3 * 2 ** (-(L + 1) / 2)
    lower = rho(tripod(L - 1))
    # Schur test vector
    theta = math.log(math.sqrt(2))
    f = np.ones(nvA)
    nxt = nvB
    for u, v in edges:
        for m in range(1, L):
            f[nxt] = math.cosh(theta * (m - L / 2)) / math.cosh(theta * L / 2)
            nxt += 1
    ratio = float(np.max((A @ f) / f))
    # spectrum identity
    eA = np.sort(np.linalg.eigvalsh(A))
    eB = np.linalg.eigvalsh(B)
    p = p_L(L)
    pred = []
    for t in eB:
        pred.extend(np.real((p - t).roots))
    mult = (k // 2) * len(elems)
    for j in range(1, L):
        pred.extend([2 * math.cos(math.pi * j / L)] * mult)
    pred = np.sort(np.array(pred))
    err = float(np.max(np.abs(pred - eA))) if len(pred) == len(eA) else float("inf")
    ok = conn and lower <= normA + 1e-9 and normA <= upper + 1e-9 and ratio <= upper + 1e-9 and err < 1e-6
    report.append((name, L, nvA, conn, lower, normA, upper, ratio, err, ok))
    return ok


def main():
    allok = True
    print("# tripod norms rho(T_{k,k,k}) vs 3/sqrt2 = %.10f" % LAM)
    prev = 0
    for k in [1, 2, 3, 4, 5, 6, 8, 10, 15, 20, 30]:
        r = rho(tripod(k))
        rl = rayleigh_lower(k)
        good = rl <= r + 1e-12 and r < LAM and r >= prev
        allok &= good
        prev = r
        print("k=%2d rho=%.10f rayleigh_lower=%.10f gap=%.3e ok=%s" % (k, r, rl, LAM - r, good))
    print("# first k with rho(T_kkk) > 2.019 and > 2.1:")
    for target in (2.019, 2.1, 2.12):
        k = 1
        while rho(tripod(k)) <= target:
            k += 1
        print("  target %.3f: k=%d rho=%.6f" % (target, k, rho(tripod(k))))
    report = []
    cases = [
        ("Z/7, gens (1,2)", group_cyclic(7), [1, 2]),
        ("Z/12, gens (1,5)", group_cyclic(12), [1, 5]),
        ("S3, gens ((01),(012))", group_s3(), [(1, 0, 2), (1, 2, 0)]),
        ("D5, gens (refl, rot)", group_dihedral(5), [(0, -1), (1, 1)]),
        ("Z/9, gens (1,3,0)", group_cyclic(9), [1, 3, 0]),
    ]
    for L in (2, 3, 4, 6, 8):
        for name, (elems, mul), gens in cases:
            allok &= check_case(name, elems, mul, gens, L, report)
    print("# subdivision checks: name, L, size, connected, tripod_lower, norm, schur_upper, max(Af/f), spectrum_err, ok")
    for row in report:
        print("%-24s L=%d n=%4d conn=%s low=%.6f norm=%.6f up=%.6f Af/f=%.6f err=%.2e ok=%s" % row)
    print("ALL OK" if allok else "SOME CHECK FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
