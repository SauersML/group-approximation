"""Sanity checks for set-indexed-repetition-escapes-the-base-sdp-bound.

Blow-up odd cycle G_{m,M}: Alice (x,a), Bob (y,b), x uniform in Z_m, y = x w.p. 1/2,
y = x+-1 w.p. 1/4 each, tags a,b uniform and independent; bits equal iff y = x.

[1] basic-SDP vectors w_x = angle x*pi*(m-1)/m: orthogonality, normalisation, value
    >= 1 - pi^2/(8 m^2).
[2] Lemma W: for random Alice position groups and colourings (mono, one-defect,
    random), Monte Carlo Pr_delta[all R_z monochromatic] <= 6 (3/4)^g.
[3] E[Phi] with Phi = prod_z 1/binom(n_z, r_z) for the best natural Alice strategies
    (parity colouring with one defect point, which is optimal up to constants),
    against the proved bound 2*(2m/n + 2 m e^{-n/8m} + 6 (3/4)^{n/2m}).
Illustrative only; the proof is in the route.
"""
import math, random
import numpy as np

rng = random.Random(20260917)

def check_sdp(m):
    th = [x * math.pi * (m - 1) / m for x in range(m)]
    w = [np.array([math.cos(t), math.sin(t)]) for t in th]
    e = np.array([0.0, 0.0, 1.0])
    def vec(x):
        W = np.array([w[x][0], w[x][1], 0.0])
        return [(e + W) / 2, (e - W) / 2]
    worst_orth = max(abs(vec(x)[0] @ vec(x)[1]) for x in range(m))
    worst_norm = max(abs(vec(x)[0] @ vec(x)[0] + vec(x)[1] @ vec(x)[1] - 1) for x in range(m))
    val = 0.0
    for x in range(m):
        u = vec(x)
        val += 0.5 * (u[0] @ u[0] + u[1] @ u[1])            # y = x, identity
        for y in ((x + 1) % m, (x - 1) % m):                 # y = x+-1, flip
            v = vec(y)
            val += 0.25 * (u[0] @ v[1] + u[1] @ v[0])
    val /= m
    return worst_orth, worst_norm, val, 1 - math.pi ** 2 / (8 * m * m)

def sample_moves(n):
    r = np.random.default_rng(rng.randrange(1 << 30)).random(n)
    return np.where(r < 0.5, 0, np.where(r < 0.75, 1, -1))

def R_sets(m, xs, bits, mv):
    """required-bit multisets at Bob's positions: counts (n_z, r_z)."""
    nz = np.zeros(m, int); rz = np.zeros(m, int)
    for x, f, d in zip(xs, bits, mv):
        z = (x + d) % m
        req = f if d == 0 else 1 - f
        nz[z] += 1; rz[z] += req
    return nz, rz

def phi(nz, rz):
    p = 1.0
    for n_, r_ in zip(nz, rz):
        if n_ > 0:
            p /= math.comb(int(n_), int(r_))
    return p

def colouring(kind, m, xs):
    bits = [x % 2 for x in xs]                              # parity colouring: frustrated at z = 0
    if kind == "defect":                                    # flip one point at position m-1
        idx = [i for i, x in enumerate(xs) if x == m - 1]
        if idx:
            bits[idx[0]] ^= 1
    elif kind == "random":
        bits = [rng.randrange(2) for _ in xs]
    return bits

print("[1] basic SDP of the odd cycle / blow-up")
for m in (3, 5, 7, 21, 101):
    o, nn, v, lb = check_sdp(m)
    print(f"  m={m:4d} max|<u0,u1>|={o:.1e} max|norm-1|={nn:.1e} sdp>={v:.8f} bound={lb:.8f} ok={v >= lb - 1e-12}")

print("[2] Lemma W: Pr[all R_z mono] vs 6 (3/4)^g")
for m, n in ((5, 40), (7, 70), (7, 140)):
    for kind in ("mono", "defect", "random"):
        xs = [rng.randrange(m) for _ in range(n)]
        g = min(xs.count(x) for x in range(m))
        bits = colouring(kind, m, xs)
        T = 4000; hits = 0
        for _ in range(T):
            nz, rz = R_sets(m, xs, bits, sample_moves(n))
            hits += all(r_ in (0, n_) for n_, r_ in zip(nz, rz))
        print(f"  m={m} n={n} {kind:6s} g={g:3d} PrW~{hits/T:.4f} bound={6*(0.75)**g:.4f}")

print("[3] E[Phi] (upper bound on set-indexed value, natural strategies) vs proved bound")
for m in (7, 11):
    for n in (4 * m, 16 * m, 64 * m):
        best = 0.0
        for kind in ("mono", "defect"):
            T = 400; acc = 0.0
            for _ in range(T):
                xs = [rng.randrange(m) for _ in range(n)]
                bits = colouring(kind, m, xs)
                nz, rz = R_sets(m, xs, bits, sample_moves(n))
                acc += phi(nz, rz)
            best = max(best, acc / T)
        proved = 2 * (2 * m / n + 2 * m * math.exp(-n / (8 * m)) + 6 * 0.75 ** (n / (2 * m)))
        print(f"  m={m} n={n:4d} E[Phi]~{best:.4f}  m/n={m/n:.4f}  proved<={min(1,proved):.4f}  ordered>=1-B*{math.sqrt(n)/m:.3f}")
