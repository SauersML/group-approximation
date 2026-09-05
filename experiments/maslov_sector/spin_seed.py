#!/usr/bin/env python3
"""Explicit 4-dimensional projective representation of Sp_4(Z) with the Schur class of S_6 = Sp_4(F_2),
via the action on odd theta characteristics and the basic spin representation of the double cover of S_6.
Checks scalarity on relators and solves for generator signs matching the universal-cover lift pattern mod 2."""
import json, sys, itertools, numpy as np
pres = json.load(open("pres6.json")); GEN = [np.array(g, dtype=np.int64) for g in pres["generators"]]
rels = pres["relators"]; lifts = pres["lifts"]
LET = GEN + [np.rint(np.linalg.inv(g)).astype(np.int64) for g in GEN]
def blocks(g): return g[:2,:2], g[:2,2:], g[2:,:2], g[2:,2:]
def act(g, m, conv):
    A,B,C,D = blocks(g); m1 = np.array(m[:2]); m2 = np.array(m[2:])
    if conv == 0:
        n1 = D @ m1 - C @ m2 + np.diag(C @ D.T); n2 = -B @ m1 + A @ m2 + np.diag(A @ B.T)
    elif conv == 1:
        n1 = D.T @ m1 - B.T @ m2 + np.diag(C @ D.T); n2 = -C.T @ m1 + A.T @ m2 + np.diag(A @ B.T)
    elif conv == 2:
        n1 = A @ m1 + B @ m2 + np.diag(A @ B.T); n2 = C @ m1 + D @ m2 + np.diag(C @ D.T)
    else:
        n1 = A.T @ m1 + C.T @ m2 + np.diag(A.T @ C); n2 = B.T @ m1 + D.T @ m2 + np.diag(B.T @ D)
    return tuple(int(x) % 2 for x in np.concatenate([n1, n2]))
chars = list(itertools.product([0,1], repeat=4))
odd = [m for m in chars if (m[0]*m[2] + m[1]*m[3]) % 2 == 1]
print("odd characteristics:", odd)
rng = np.random.default_rng(0)
good = None
for conv in range(4):
    ok = True
    for _ in range(300):
        w = rng.integers(0, 16, size=rng.integers(2, 6))
        g = np.eye(4, dtype=np.int64)
        for a in w: g = g @ LET[a]
        for m in chars:
            # homomorphism check: act(g1 g2, m) == act(g1, act(g2, m)) with g = g1 g2 split at random point
            pass
        # check composition on generator pairs
    for a in range(16):
        for b in range(16):
            g1, g2 = LET[a], LET[b]
            for m in chars:
                if act(g1 @ g2, m, conv) != act(g1, act(g2, m, conv), conv): ok = False; break
            if not ok: break
        if not ok: break
    parity_ok = all((act(g, m, conv)[0]*act(g, m, conv)[2] + act(g, m, conv)[1]*act(g, m, conv)[3]) % 2 == (m[0]*m[2]+m[1]*m[3]) % 2 for g in LET for m in chars)
    print(f"convention {conv}: homomorphism on generator pairs = {ok}, parity preserved = {parity_ok}", flush=True)
    if ok and parity_ok and good is None: good = conv
assert good is not None, "no working convention"
conv = good
perm = []
for g in GEN:
    p = [odd.index(act(g, m, conv)) for m in odd]
    assert sorted(p) == list(range(6)); perm.append(p)
print("permutations of the six odd characteristics:", perm)
# Clifford: gamma matrices for Cl_5 in M_4(C)
sx = np.array([[0,1],[1,0]], dtype=complex); sy = np.array([[0,-1j],[1j,0]]); sz = np.array([[1,0],[0,-1]], dtype=complex); I2 = np.eye(2)
gam = [np.kron(sx, I2), np.kron(sy, I2), np.kron(sz, sx), np.kron(sz, sy), np.kron(sz, sz)]
for i in range(5):
    for j in range(5):
        assert np.allclose(gam[i] @ gam[j] + gam[j] @ gam[i], 2*(i==j)*np.eye(4))
# orthonormal basis of V = {x in R^6 : sum x = 0}
raw = [np.array([1,-1,0,0,0,0.]), np.array([1,1,-2,0,0,0.]), np.array([1,1,1,-3,0,0.]), np.array([1,1,1,1,-4,0.]), np.array([1,1,1,1,1,-5.])]
F = [v/np.linalg.norm(v) for v in raw]
def Gamma_transposition(i, j):
    v = np.zeros(6); v[i] = 1; v[j] = -1; v /= np.sqrt(2)
    c = [np.dot(v, f) for f in F]
    return sum(ci*gi for ci, gi in zip(c, gam))
def perm_to_transpositions(p):
    # p: list, p[i] = image of i. Decompose into transpositions (i j) such that composition equals p.
    p = list(p); trans = []
    cur = list(range(6))  # current permutation as list
    # build p as product: find cycles
    seen = [False]*6
    for i in range(6):
        if seen[i]: continue
        cyc = []; j = i
        while not seen[j]: seen[j] = True; cyc.append(j); j = p[j]
        for k in range(len(cyc)-1, 0, -1):
            trans.append((cyc[0], cyc[k]))
    return trans
def perm_matrix(p):
    M = np.zeros((6,6)); 
    for i in range(6): M[p[i], i] = 1
    return M
rho = []
for p in perm:
    T = perm_to_transpositions(p)
    # verify the transposition product equals p (as permutation matrices)
    M = np.eye(6)
    for (i, j) in T:
        t = list(range(6)); t[i], t[j] = j, i; M = M @ perm_matrix(t)
    assert np.allclose(M, perm_matrix(p)), "transposition decomposition wrong"
    U = np.eye(4, dtype=complex)
    for (i, j) in T: U = U @ Gamma_transposition(i, j)
    assert np.allclose(U @ U.conj().T, np.eye(4)); rho.append(U)
rho = np.stack(rho)
M16 = np.concatenate([rho, np.conj(np.transpose(rho, (0,2,1)))])
def ev(w):
    P = np.eye(4, dtype=complex)
    for a in w: P = P @ M16[a]
    return P
# scalarity check on a sample + all lifted
idx = [i for i, k in enumerate(lifts) if k != 0] + list(rng.choice(len(rels), size=6000, replace=False))
lam = {}; nonscalar = 0
for i in idx:
    P = ev(rels[i]); l = P[0,0]
    if not np.allclose(P, l*np.eye(4), atol=1e-8) or abs(abs(l)-1) > 1e-8: nonscalar += 1
    else: lam[i] = l
print(f"scalar on {len(lam)} of {len(idx)} tested relators; nonscalar: {nonscalar}", flush=True)
vals = sorted(set(np.round(np.angle(l)/np.pi, 4) for l in lam.values()))
print("scalar phases / pi observed:", vals, flush=True)
# solve signs: for relator r with exponent sums n_r, need prod_s eps_s^{n_rs} * lam_r = (-1)^{k_r}
def expsum(r):
    n = [0]*8
    for a in r: n[a % 8] += 1 if a < 8 else -1
    return n
rows = []; rhs = []
for i, l in lam.items():
    n = expsum(rels[i]); lg = 0 if abs(l-1) < 1e-6 else (1 if abs(l+1) < 1e-6 else None)
    if lg is None: continue
    rows.append([x % 2 for x in n]); rhs.append((lg + lifts[i]) % 2)
A = np.array(rows, dtype=np.int64); b = np.array(rhs, dtype=np.int64)
# Gaussian elimination over F2
Ab = np.concatenate([A, b[:, None]], axis=1) % 2; r = 0; piv = []
for c in range(8):
    rowsel = [i for i in range(r, Ab.shape[0]) if Ab[i, c] == 1]
    if not rowsel: continue
    Ab[[r, rowsel[0]]] = Ab[[rowsel[0], r]]
    for i in range(Ab.shape[0]):
        if i != r and Ab[i, c] == 1: Ab[i] ^= Ab[r]
    piv.append(c); r += 1
inconsistent = any(Ab[i, :8].sum() == 0 and Ab[i, 8] == 1 for i in range(Ab.shape[0]))
print("sign system consistent with the mod-2 universal-cover lift pattern:", not inconsistent, flush=True)
if not inconsistent:
    x = np.zeros(8, dtype=np.int64)
    for i, c in enumerate(piv): x[c] = Ab[i, 8]
    eps = [(-1)**int(v) for v in x]
    seed = np.stack([eps[s]*rho[s] for s in range(8)])
    M16s = np.concatenate([seed, np.conj(np.transpose(seed, (0,2,1)))])
    mx = 0.0
    for i in range(len(rels)):
        P = np.eye(4, dtype=complex)
        for a in rels[i]: P = P @ M16s[a]
        D = P - ((-1)**lifts[i])*np.eye(4); mx = max(mx, np.sqrt(np.real(np.trace(D.conj().T @ D))/4))
    print(f"seed verified on ALL {len(rels)} relators: max normalized-HS defect in the mod-2 sector = {mx:.2e}", flush=True)
    json.dump({"seed": [[ [float(z.real), float(z.imag)] for z in row] for U in seed for row in U], "d": 4}, open("seed_m2_d4.json", "w"))
    print("wrote seed_m2_d4.json")
else:
    # what pattern does it match? try the trivial pattern (k_r = 0 for all)
    b2 = np.array([0 if abs(l-1) < 1e-6 else 1 for l in lam.values()], dtype=np.int64)
    print("(diagnostic) signs matching the trivial pattern would need lam_r pattern:", sorted(set(b2.tolist())))
