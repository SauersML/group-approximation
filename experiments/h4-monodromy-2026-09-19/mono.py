# Braid monodromy of the l_X-fibration of a rank-4 Coxeter arrangement.
# A pure Artin word g (letters +-1..4) gives the standard loop L(g) in M (complement in C^4).
# Writing q = b~ + z*l with l = omega_1 (fixed by W_X), the fibre point is z and the non-X wall r
# meets the fibre at z - r(q)/r(l).  Translating the moving point to 0, the wall-strand r sits at
# P_r = -B(r,q)/r_1.  L(g) therefore gives a pure braid on 1 + #nonX strands (strand 'm' = moving
# point).  Along each half-turn the real parts are linear in t and the imaginary parts are
# proportional to sin(pi t), so all crossings are computed in closed form.
import numpy as np, random, sys
MS = {'H4': {(0, 1): 3, (1, 2): 3, (2, 3): 5}, 'A4': {(0, 1): 3, (1, 2): 3, (2, 3): 3},
      'B4': {(0, 1): 3, (1, 2): 3, (2, 3): 4}, 'D4': {(0, 1): 3, (1, 2): 3, (1, 3): 3},
      'H4r': {(0, 1): 5, (1, 2): 3, (2, 3): 3}}

class Arr:
    def __init__(s, name='H4', xc=None, yc=None, eps=0.37):
        n = 4; B = np.eye(n)
        for (i, j), m in MS[name].items(): B[i, j] = B[j, i] = -np.cos(np.pi / m)
        s.B = B; s.n = n
        S = []
        for j in range(n):
            M = np.eye(n); M[j, :] -= 2 * B[j, :]; S.append(M)   # v -> v - 2 B(a_j,v) a_j
        s.S = S
        R = [np.eye(n)[i] for i in range(n)]; seen = {tuple(np.round(r, 7)) for r in R}; k = 0
        while k < len(R):
            r = R[k]; k += 1
            for j in range(n):
                nr = S[j] @ r; key = tuple(np.round(nr, 7))
                if key not in seen and tuple(np.round(-nr, 7)) not in seen and (nr > -1e-9).all():
                    seen.add(key); R.append(nr)
        s.roots = R                                   # positive roots, alpha-coordinates
        s.nonX = [r for r in R if abs(r[0]) > 1e-9]   # walls not containing l = omega_1
        s.X = [r for r in R if abs(r[0]) <= 1e-9]
        rng = np.random.RandomState(7)
        xc = np.array(xc if xc is not None else [3.0, 0.1, 0.2, 5.0]) + 1e-3 * rng.rand(4)
        yc = np.array(yc if yc is not None else [1.0, 1.3, 0.7, 1.1]) + 1e-3 * rng.rand(4)
        s.x = np.linalg.solve(B, xc); s.y = np.linalg.solve(B, yc); s.eps = eps
        s.N = len(s.nonX) + 1                          # strand N-1 is the moving point m
        A0 = [-(r @ B @ s.x) / r[0] for r in s.nonX] + [0.0]
        s.eta = 1e-9 * np.random.RandomState(11).rand(s.N)
        s.order0 = sorted(range(s.N), key=lambda k: A0[k])   # left-to-right labels at the base

    def braid(s, word):
        """Crossing word [(k, sign)] (k = position, 0-based) of the loop of `word`; also returns final W."""
        B = s.B; winv = np.eye(s.n); out = []; order = list(s.order0)
        for L in word:
            i = abs(L) - 1; sg = 1 if L > 0 else -1
            bx = s.x @ B[:, i]          # B(alpha_i, x)
            Yv = s.y if sg > 0 else s.S[i] @ s.y   # sigma_i^-1 = s_i-image of the reversed sigma_i path
            A = []; D = []; I = []
            for r in s.nonX:
                rp = winv @ r
                A.append(-(rp @ B @ s.x) / r[0]); D.append(2 * bx * (rp @ B[:, i]) / r[0])
                I.append(-s.eps * (rp @ B @ Yv) / r[0])
            A.append(0.0); D.append(0.0); I.append(0.0)
            ev = []
            for p in range(s.N):
                for q in range(p + 1, s.N):
                    dd = D[p] - D[q]
                    if abs(dd) < 1e-13: continue
                    t = (A[q] - A[p]) / dd
                    # triple points of the real projection (e.g. z_r, z_{s_i r} rotating about a cluster
                    # partner at t = 1/2) are resolved by generic tiny offsets eta_p of the real parts;
                    # the heights at a triple point are distinct, so the braid does not depend on eta
                    if 1e-12 < t < 1 - 1e-12: ev.append((t + (s.eta[q] - s.eta[p]) / dd, p, q))
            ev.sort()
            for t, p, q in ev:
                ip, iq = order.index(p), order.index(q)
                assert abs(ip - iq) == 1, ('non-adjacent crossing', t, p, q)
                k = min(ip, iq); left = order[k]; right = order[k + 1]
                di = np.sin(np.pi * t) * (I[left] - I[right])
                assert abs(di) > 1e-10, ('degenerate crossing (collision)', t, p, q)
                out.append((k, 1 if di > 0 else -1)); order[k], order[k + 1] = right, left
            winv = s.S[i] @ winv
        return out, winv, order

# ---- exact-free randomized identity test: Artin action composed into SL2(F_p) images ----
P = (1 << 61) - 1
def mm(a, b):
    return ((a[0]*b[0]+a[1]*b[2]) % P, (a[0]*b[1]+a[1]*b[3]) % P, (a[2]*b[0]+a[3]*b[2]) % P, (a[2]*b[1]+a[3]*b[3]) % P)
def mi(a): return (a[3], (-a[1]) % P, (-a[2]) % P, a[0])
def randsl2(rng):
    a, b, c = rng.randrange(1, P), rng.randrange(P), rng.randrange(P)
    return (a, b, c, (1 + b * c) * pow(a, P - 2, P) % P)

class Img:
    """T[k] = rho(phi(x_k)) for phi = sigma_{w1} o sigma_{w2} o ... ; rho random into SL2(F_p)."""
    def __init__(s, n, seed=1):
        rng = random.Random(seed); s.T = [randsl2(rng) for _ in range(n)]
    def apply(s, word):
        T = s.T
        for k, e in word:
            a, b = T[k], T[k + 1]
            if e > 0: T[k], T[k + 1] = mm(mm(a, b), mi(a)), a
            else: T[k], T[k + 1] = b, mm(mm(mi(b), a), b)
        return s

def same(n, w1, w2, seeds=(1, 2, 3)):
    return all(Img(n, sd).apply(w1).T == Img(n, sd).apply(w2).T for sd in seeds)

def inv(w): return [-g for g in reversed(w)]
def binv(bw): return [(k, -e) for k, e in reversed(bw)]
def com(x, y): return x + y + inv(x) + inv(y)

def forget(bw, order0, lab):
    """Delete strand `lab` from a crossing word (positions) started at label order order0."""
    order = list(order0); out = []
    for k, e in bw:
        l, r = order[k], order[k + 1]
        if lab not in (l, r):
            kk = k - (1 if order.index(lab) < k else 0); out.append((kk, e))
        order[k], order[k + 1] = r, l
    return out
