"""Rotation-coded boundary class in F_2 = <a,b>: exact checks for
research/fpbs-rotation-boundary-class-refutes-shadow-summability.

Ray zeta(theta, j): letter n (n >= 1) is t_{n+j}^{s(theta + n alpha)}, with t_odd = a, t_even = b,
s(x) = +1 on [0,1/2), -1 on [1/2,1).  mu = law of zeta for (theta, j) uniform on T x Z/2.
In the Cayley tree, O_0(g) is the cylinder [g], so S_0(lam) = sum_g lam[g] lam[g^-1].

Checks:
 (1) inversion identity: (zeta_1..zeta_m(theta,j))^{-1} = zeta_1..zeta_m(-theta-(m+1)alpha, j+m+1);
 (2) level sums L_m = sum_{|w|=m} mu[w] mu[w^-1] >= 1/(4m), partial sums grow like log M;
 (3) the same for mu restricted to A = [0, 0.05) x {0}: partial sums still grow like log M;
 (4) pointwise: for random pairs, the number of reversal matches at all lengths is finite
     (first disagreement index), with tail P(count >= k) ~ c/k (so its mean diverges).
Usage: python3 rotation_class.py [M] [pairs]
"""
import sys, math, random
import numpy as np

M = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
PAIRS = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
ALPHA = (math.sqrt(5) - 1) / 2

def s(x):
    return 1 if (x % 1.0) < 0.5 else -1

def word(theta, j, m):
    out = []
    for n in range(1, m + 1):
        t = 'a' if (n + j) % 2 == 1 else 'b'
        out.append(t if s(theta + n * ALPHA) > 0 else t.upper())
    return ''.join(out)

INV = str.maketrans('aAbB', 'AaBb')

def inverse(w):
    return w[::-1].translate(INV)

def reduced(w):
    return all(w[i].translate(INV) != w[i + 1] for i in range(len(w) - 1))

# (1) inversion identity and reducedness
rng = random.Random(1)
bad = 0
for _ in range(2000):
    th, j, m = rng.random(), rng.randrange(2), rng.randrange(1, 60)
    w = word(th, j, m)
    if not reduced(w) or inverse(w) != word(-th - (m + 1) * ALPHA, (j + m + 1) % 2, m):
        bad += 1
print(f"(1) inversion identity + reducedness: {bad} failures in 2000 random (theta,j,m)")

# (2),(3) level sums via arcs of the partition of T by {-n alpha, 1/2 - n alpha : n <= m}
def arcs(m):
    n = np.arange(1, m + 1)
    pts = np.sort(np.concatenate([(-n * ALPHA) % 1.0, (0.5 - n * ALPHA) % 1.0]))
    lo = pts
    hi = np.concatenate([pts[1:], [pts[0] + 1.0]])
    return lo, hi

def overlap(lo, hi, a, b):
    """length of [lo,hi) (hi may exceed 1) intersected with the arc [a, a+(b-a)) mod 1, b-a < 1"""
    tot = np.zeros_like(lo)
    for shift in (-1.0, 0.0, 1.0):
        tot += np.clip(np.minimum(hi, b + shift) - np.maximum(lo, a + shift), 0, None)
    return tot

A0, A1 = 0.0, 0.05
cum_full = cum_A = 0.0
rows = []
checkpoints = {10, 30, 100, 300, 1000, M}
minratio = float('inf')
for m in range(1, M + 1):
    lo, hi = arcs(m)
    L = 2 * 0.25 * np.sum((hi - lo) ** 2)      # two j's, each arc x {j} has mass |arc|/2; mu[w^-1]=mu[w]
    # arcs merge into cells, so sum over words >= sum over arcs; lower bound is what we need
    minratio = min(minratio, L * 4 * m)
    cum_full += L
    if m % 2 == 1:                              # tau_m keeps j; A-slice j=0, tau_m A = [-A1-(m+1)a, -A0-(m+1)a)
        c = (-(m + 1) * ALPHA) % 1.0
        x = overlap(lo, hi, A0, A1)
        y = overlap(lo, hi, (c - A1) % 1.0, (c - A1) % 1.0 + (A1 - A0))
        cum_A += 0.25 * np.sum(x * y)
    if m in checkpoints:
        rows.append((m, cum_full, cum_A))
print(f"(2) min over m<={M} of 4m * L_m = {minratio:.4f}  (>= 1 proves L_m >= 1/(4m) on arcs)")
print("    m      sum_{k<=m} L_k    /log m     S_0(mu|A) partial   /log m")
for m, f, a in rows:
    print(f"  {m:5d}   {f:12.5f}   {f / math.log(m + 1):8.5f}   {a:14.7f}   {a / math.log(m + 1):9.7f}")

# (4) pointwise match counts: reversal matches of zeta(theta,0) against zeta(theta',1) at even k
# happen iff s(theta' - i alpha) = s(-theta - alpha - i alpha) for i = 0..k-1 (proof, Theorem 3)
K = 20000
cnt, prod = [], []
for _ in range(PAIRS):
    th, thp = rng.random(), rng.random()
    x, y = thp, -th - ALPHA
    i = 0
    while i < K and s(x - i * ALPHA) == s(y - i * ALPHA):
        i += 1
    d = abs(((x - y) + 0.5) % 1.0 - 0.5)
    cnt.append(i)
    prod.append(i * d)
cnt = np.array(cnt)
print(f"(4) {PAIRS} random pairs: count = first disagreement index; max count = {cnt.max()};")
print(f"    max of count * ||x - y|| = {max(prod):.4f}  (bounded: count <= C/||x-y||, finite off x = y)")
for k in (1, 3, 10, 30, 100, 300):
    p = (cnt >= k).mean()
    print(f"    P(count >= {k:3d}) = {p:.5f}   k * P = {k * p:.4f}")
