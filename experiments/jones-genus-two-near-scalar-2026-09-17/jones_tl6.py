"""Jones' rectangular (3,3) representation of Mod(S_2), as a 5-dim Temperley-Lieb module.

Birman-Hilden: Mod(S_2) = B_6 / << (s1..s5)^6, iota^2, [iota, s1] >>, iota = s1 s2 s3 s4 s5 s5 s4 s3 s2 s1.
TL_6 acts on the 5 noncrossing perfect matchings of 6 points; g_i = A + A^{-1} e_i, delta = -A^2 - A^{-2}.
We rescale s_i -> beta g_i so that the three genus-two relations hold, then study the separating twist
t_s = (s1 s2)^6 (boundary twist of the genus-one subsurface lying over the disc around points 1,2,3).

Output: for A = exp(i alpha) on the unitary arc delta in (sqrt 2, 2], i.e. |alpha - pi/2| < pi/8 (Gram det = d^5 (d-1)^4 (d+1)^4 (d^2-2), positive definite there),
 - residuals of all Mod(S_2) relations and of unitarity,
 - spectrum of rho(t_s), its distance to the nearest scalar, and to omega^{+-1} I.
"""
import itertools, cmath, math
import numpy as np

N = 6
def matchings(pts):
    if not pts:
        yield []
        return
    a = pts[0]
    for k in range(1, len(pts), 2):          # noncrossing: partner splits the rest evenly
        b = pts[k]
        for L in matchings(pts[1:k]):
            for R in matchings(pts[k + 1:]):
                yield [(a, b)] + L + R
BASIS = [tuple(sorted(m)) for m in matchings(list(range(N)))]
IDX = {m: j for j, m in enumerate(BASIS)}
D = len(BASIS)
assert D == 5

def partner(m):
    p = {}
    for a, b in m:
        p[a], p[b] = b, a
    return p

def E(i, delta):
    """e_i caps points i,i+1 on top and cups them; returns (matrix)."""
    M = np.zeros((D, D), complex)
    for j, m in enumerate(BASIS):
        p = partner(m)
        if p[i] == i + 1:
            M[j, j] += delta
        else:
            a, b = p[i], p[i + 1]
            new = [e for e in m if i not in e and i + 1 not in e] + [(i, i + 1), tuple(sorted((a, b)))]
            M[IDX[tuple(sorted(new))], j] += 1
    return M

def loops(m1, m2):
    p1, p2 = partner(m1), partner(m2)
    seen, c = set(), 0
    for s in range(N):
        if s in seen:
            continue
        c += 1
        x, use1 = s, True
        while True:
            seen.add(x)
            x = p1[x] if use1 else p2[x]
            seen.add(x)
            use1 = not use1
            if x == s and use1:
                break
    return c

def gram(delta):
    return np.array([[delta ** loops(a, b) for b in BASIS] for a in BASIS], complex)

def rep(alpha):
    A = cmath.exp(1j * alpha)
    delta = (-A * A - 1 / (A * A)).real
    g = [A * np.eye(D) + E(i, delta) / A for i in range(N - 1)]
    return A, delta, g

def prod(ms):
    out = np.eye(D, dtype=complex)
    for m in ms:
        out = out @ m
    return out

def scalar_of(M):
    lam = np.trace(M) / D
    return lam, np.linalg.norm(M - lam * np.eye(D), 2)

def mod_s2(alpha):
    """Return all admissible rescalings beta and the rescaled generators."""
    A, delta, g = rep(alpha)
    c, ec = scalar_of(np.linalg.matrix_power(prod(g), 6))          # (g1..g5)^6
    iota = prod(g + g[::-1])
    j, ej = scalar_of(iota)
    betas = []
    for k in range(30):                                          # beta^30 c = 1 ; beta^20 j^2 = 1 (10 survive)
        b = cmath.exp(1j * (-cmath.phase(c) + 2 * math.pi * k) / 30)
        if abs(b ** 20 * j * j - 1) < 1e-8:
            betas.append(b)
    return A, delta, g, betas, (ec, ej)

def check(alpha, beta, g, G):
    s = [beta * x for x in g]
    I = np.eye(D)
    res = []
    for i in range(N - 2):
        res.append(np.linalg.norm(s[i] @ s[i + 1] @ s[i] - s[i + 1] @ s[i] @ s[i + 1]))
    for i, k in itertools.combinations(range(N - 1), 2):
        if k - i >= 2:
            res.append(np.linalg.norm(s[i] @ s[k] - s[k] @ s[i]))
    res.append(np.linalg.norm(np.linalg.matrix_power(prod(s), 6) - I))
    iota = prod(s + s[::-1])
    res.append(np.linalg.norm(iota @ iota - I))
    res.append(np.linalg.norm(iota @ s[0] - s[0] @ iota))
    uni = max(np.linalg.norm(x.conj().T @ G @ x - G) for x in s)
    return max(res), uni

def unitarize(M, G):
    """Matrix of M in a G-orthonormal basis (G positive definite)."""
    w, V = np.linalg.eigh(G)
    R = V @ np.diag(np.sqrt(w)) @ V.conj().T
    return R @ M @ np.linalg.inv(R)

OMEGA = [cmath.exp(2j * math.pi / 3), cmath.exp(-2j * math.pi / 3)]

def ts_data(alpha, beta, g, G):
    T = unitarize(np.linalg.matrix_power(beta * g[0] @ (beta * g[1]), 6), G)
    ev = np.linalg.eigvals(T)
    lam, dscal = scalar_of(T)
    # exact nearest-scalar operator distance: minimize over unit lambda
    grid = np.exp(1j * np.linspace(0, 2 * math.pi, 20001))
    dist = np.max(np.abs(ev[None, :] - grid[:, None]), axis=1)
    k = int(np.argmin(dist))
    dom = min(np.linalg.norm(T - w * np.eye(D), 2) for w in OMEGA)
    return ev, grid[k], dist[k], dom

if __name__ == "__main__":
    lo = math.pi / 2
    width = math.pi / 8
    print("alpha-pi/2  delta     |betas| relres   unires   min_eig(G)  nearest-scalar(arg/2pi) dist-to-scalar  min_beta dist-to-omega")
    worst_omega = 10.0
    for x in list(np.linspace(0.0, 0.999 * width, 13)) + [math.pi / 12]:
        alpha = lo + x
        A, delta, g, betas, (ec, ej) = mod_s2(alpha)
        G = gram(delta)
        mG = min(np.linalg.eigvalsh(G))
        rows = []
        for b in betas:
            rr, uu = check(alpha, b, g, G)
            ev, lam, dsc, dom = ts_data(alpha, b, g, G)
            rows.append((rr, uu, lam, dsc, dom))
        rr = max(r[0] for r in rows); uu = max(r[1] for r in rows)
        dom = min(r[4] for r in rows); worst_omega = min(worst_omega, dom)
        lam0, dsc0 = rows[0][2], rows[0][3]
        print(f"{x:9.5f}  {delta:8.5f}  {len(betas):3d}   {rr:.1e}  {uu:.1e}  {mG:9.2e}   "
              f"{(cmath.phase(lam0) / (2 * math.pi)) % 1:8.5f}              {dsc0:8.5f}        {dom:8.5f}")
    print("nearest-scalar values over all betas at delta = 2:",
          sorted({round((cmath.phase(b ** 12) / (2 * math.pi)) % 1, 6) for b in mod_s2(lo)[3]}))
    print("infimum over the unitary arc and all betas of ||rho(t_s) - omega^{+-1}||_op :", round(worst_omega, 5))
    A, delta, g, betas, _ = mod_s2(lo + 0.1)
    print("g_1 eigenvalue ratio -A^{-4} at alpha = pi/2 + 0.1 has phase/2pi =",
          (cmath.phase(-A ** -4) / (2 * math.pi)) % 1, "(irrational => infinite image)")
