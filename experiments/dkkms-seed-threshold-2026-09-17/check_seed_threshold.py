#!/usr/bin/env python3
"""Checks for dkkms-class-seed-threshold-is-sqrt-l-over-2-to-half-l.

Column model of the DKKMS edge law given U (Step 7 of
dkkms-2to1-value-is-at-least-seed-concentration-proof): l columns, block by
block. A kept block has l i.i.d. uniform images in Y_i = F_2^2 (encoded 0..3).
A smoothed block with variable v (ebar_v in {1,2,3}) has images c_j * ebar_v
for j < l and a uniform last image.

(a) exact per-block moments under the reference law (beta = 0):
    E r = 1, E r^2 - 1 = beta^2 (2^(l-1) - 1)/3, Pr[kept Z = 1] = 3*2^(1-l) - 2*4^(1-l).
(b) Monte Carlo of E max_Q w(Q|C) (MAP seed mass) and of the counting rule,
    against the flatness bound (Theorem F) and the Bernstein bound (Lemma B).
(c) the threshold in the scaled variable t = beta sqrt(k) 2^(l/2) / sqrt(l).
Prints ALL PASS if every check holds.
"""
import itertools
import math
import sys

import numpy as np

RNG = np.random.default_rng(20260917)
FAIL = []


def check(name, ok, info=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + info if info else ""))
    if not ok:
        FAIL.append(name)


def n_lines(imgs):
    """imgs: (..., r) ints in 0..3. Number of lines <e> (e in 1..3) containing all."""
    nz = imgs != 0
    anynz = nz.any(axis=-1)
    first = np.where(nz, imgs, 0).max(axis=-1)  # some nonzero value (max)
    same = np.where(nz, imgs == first[..., None], True).all(axis=-1)
    return np.where(~anynz, 3, np.where(same, 1, 0))


def part_a():
    for l in range(2, 8):
        vecs = np.array(list(itertools.product(range(4), repeat=l - 1)))
        N = n_lines(vecs)
        beta = 0.37
        r = 1 - beta + beta * 2 ** (l - 1) * N / 3.0
        m1 = r.mean()
        m2 = (r ** 2).mean() - 1
        want = beta ** 2 * (2 ** (l - 1) - 1) / 3.0
        pz = (N >= 1).mean()
        wz = 3 * 2.0 ** (1 - l) - 2 * 4.0 ** (1 - l)
        check(f"(a) l={l} E r = 1, chi2 block, kept Pr[Z=1]",
              abs(m1 - 1) < 1e-12 and abs(m2 - want) < 1e-12 and abs(pz - wz) < 1e-12,
              f"E r={m1:.6f} chi2={m2:.6g} want {want:.6g} pZ={pz:.6g}")


def hyperplane_bases(l):
    """For each nonzero psi in F_2^l, a basis (l-1 vectors) of ker psi."""
    out = []
    for p in range(1, 2 ** l):
        psi = [(p >> j) & 1 for j in range(l)]
        ker = [c for c in itertools.product((0, 1), repeat=l)
               if sum(a * b for a, b in zip(c, psi)) % 2 == 0]
        basis, span = [], {tuple([0] * l)}
        for c in ker:
            if c not in span:
                basis.append(c)
                span |= {tuple((a + b) % 2 for a, b in zip(s, c)) for s in span}
        out.append((psi, np.array(basis)))
    return out


def sample(l, k, beta, n):
    M = RNG.integers(0, 4, size=(n, k, l))
    sm = RNG.random((n, k)) < beta
    v = RNG.integers(1, 4, size=(n, k))
    c = RNG.integers(0, 2, size=(n, k, l - 1))
    Ms = c * v[..., None]
    M[..., : l - 1] = np.where(sm[..., None], Ms, M[..., : l - 1])
    return M


def images(M, basis):
    out = np.zeros(M.shape[:2] + (basis.shape[0],), dtype=np.int64)
    for a, cvec in enumerate(basis):
        acc = np.zeros(M.shape[:2], dtype=np.int64)
        for j, cj in enumerate(cvec):
            if cj:
                acc ^= M[..., j]
        out[..., a] = acc
    return out


def flat_bound(l, k, beta):
    H = 2 ** l - 1
    x = k * math.log1p(beta ** 2 * (2 ** (l - 1) - 1) / 3.0)
    b1 = 1.0 / H + math.sqrt(math.expm1(x) / H)
    b2 = 2 * math.sqrt(math.exp(min(x, 700)) / H)
    return min(1.0, b1, b2)


def bern_bound(l, k, beta):
    D = 0.5 - 2.0 ** (1 - l)
    e = (2 ** l - 2) * math.exp(-beta ** 2 * D ** 2 * k / (96 * 2.0 ** (-l) + 7 * beta / 3)) \
        + math.exp(-beta * k / 8)
    return max(0.0, 1 - e)


def run(l, k, beta, n):
    M = sample(l, k, beta, n)
    hb = hyperplane_bases(l)
    logF, score = [], []
    for psi, basis in hb:
        N = n_lines(images(M, basis))
        logF.append(np.log(1 - beta + beta * 2 ** (l - 1) * N / 3.0).sum(axis=1))
        score.append((N >= 1).sum(axis=1))
    logF, score = np.array(logF), np.array(score)
    i0 = [a for a, (psi, _) in enumerate(hb) if psi == [0] * (l - 1) + [1]][0]
    m = logF.max(axis=0)
    w = np.exp(logF - m)
    emax = (w.max(axis=0) / w.sum(axis=0)).mean()
    s0 = score[i0]
    others = np.delete(score, i0, axis=0)
    cnt = (s0 > others.max(axis=0)).mean()
    return emax, cnt


def part_b():
    grid = [(3, 400, 0.05), (3, 400, 0.3), (4, 800, 0.1), (4, 800, 0.3),
            (5, 1500, 0.05), (5, 1500, 0.2), (6, 2000, 0.04), (6, 2000, 0.15)]
    for l, k, beta in grid:
        n = 300
        emax, cnt = run(l, k, beta, n)
        fb, bb = flat_bound(l, k, beta), bern_bound(l, k, beta)
        slack = 3 * math.sqrt(0.25 / n)
        check(f"(b) l={l} k={k} beta={beta}: bern <= count <= Emax <= flat",
              bb <= cnt + slack and cnt <= emax + slack and emax <= fb + slack,
              f"bern={bb:.3f} count={cnt:.3f} Emax={emax:.3f} flat={fb:.3f}")


def part_c():
    k = 3000
    for l in (4, 6, 8):
        row = []
        for t in (0.1, 0.5, 2.0, 8.0):
            beta = t * math.sqrt(l) * 2 ** (-l / 2) / math.sqrt(k)
            emax, cnt = run(l, k, beta, 60 if l == 8 else 150)
            row.append((t, emax, cnt, flat_bound(l, k, beta)))
        txt = " ".join(f"t={t}:Emax={e:.2f},cnt={c:.2f},flat={f:.2f}" for t, e, c, f in row)
        check(f"(c) l={l} k={k} transition in t = beta sqrt(k) 2^(l/2)/sqrt(l)",
              row[0][1] < 0.5 and row[-1][1] > 0.9 and all(r[1] <= r[3] + 0.1 for r in row), txt)


def part_d():
    """Constants of Corollaries TH and D, and the window condition for 20 <= l < 200."""
    ok = True
    for l in range(20, 200):
        kA = math.exp(l) * (2 * l * math.log(2) + math.log(4 * 192 ** 2))
        ok &= kA >= math.exp(math.e ** 2) and kA >= 2 ** l * math.log(math.log(kA)) ** 2
    lo, hi = math.sqrt(6 * math.log(2)), math.sqrt(768 * math.log(2))
    ok &= lo > 2.03 and hi < 23.1 and hi / lo < 12
    ok &= 3 * math.log(2) > 2 and 1 - math.exp(-2) - 0.25 > 0.61
    check("(d) window k_A >= max(e^e^2, 2^l (lnln k_A)^2), thresholds 2.039/23.07, 0.6147", ok,
          f"lo={lo:.4f} hi={hi:.4f} ratio={hi / lo:.3f}")


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
    print("ALL PASS" if not FAIL else f"FAILED: {FAIL}")
    sys.exit(0 if not FAIL else 1)
