#!/usr/bin/env python3
"""Relators of Sp_4(Z) on the eight root generators, with universal-cover lifts.

Generators: x_alpha(1) for the eight roots of C_2 (unipotent 4x4 integer
matrices), letters 0..7; letters 8..15 are their inverses x_alpha(-1).
Relators: closed loops in the Cayley graph found by BFS up to radius L
(words of length <= 2L+1), free- and cyclically-reduced, deduplicated.
Lift exponent k_r: winding number of det_C of the polar-unitary part of the
concatenated one-parameter path g(t) in Sp_4(R) along the relator; this is
the class of the loop in pi_1(Sp_4(R)) = Z, i.e. the exponent of the central
generator zeta in the universal-cover extension: r~ = zeta^{k_r}.
"""
import sys, json, time, itertools
import numpy as np
from collections import deque

L = int(sys.argv[1]) if len(sys.argv) > 1 else 5
LMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 11
OUT = sys.argv[3] if len(sys.argv) > 3 else "presentation.json"

def E(i, j):
    m = np.zeros((4, 4), dtype=np.int64); m[i, j] = 1; return m
I4 = np.eye(4, dtype=np.int64)
# upper unipotent (S symmetric) and block-diagonal root elements
def root_paths():
    # returns list of (name, generator function t -> 4x4 matrix), t real
    def up(S):  # [[I, S],[0, I]]
        return lambda t: np.block([[np.eye(2), t*S], [np.zeros((2,2)), np.eye(2)]])
    def lo(S):
        return lambda t: np.block([[np.eye(2), np.zeros((2,2))], [t*S, np.eye(2)]])
    E12 = np.zeros((2,2)); E12[0,1] = 1
    E21 = E12.T
    E11 = np.diag([1.0,0.0]); E22 = np.diag([0.0,1.0])
    def dg(A_of_t):
        def f(t):
            A = A_of_t(t)
            return np.block([[A, np.zeros((2,2))],[np.zeros((2,2)), np.linalg.inv(A).T]])
        return f
    roots = [
        ("2e1",   up(E11)),                     # long
        ("2e2",   up(E22)),                     # long
        ("e1+e2", up(E12 + E21)),               # short
        ("e1-e2", dg(lambda t: np.eye(2) + t*E12)),  # short
        ("-2e1",  lo(E11)),
        ("-2e2",  lo(E22)),
        ("-e1-e2", lo(E12 + E21)),
        ("-e1+e2", dg(lambda t: np.eye(2) + t*E21)),
    ]
    return roots

roots = root_paths()
J = np.block([[np.zeros((2,2)), np.eye(2)], [-np.eye(2), np.zeros((2,2))]])
# integer generator matrices
GEN = [np.rint(f(1.0)).astype(np.int64) for _, f in roots]
GENINV = [np.rint(f(-1.0)).astype(np.int64) for _, f in roots]
LET = GEN + GENINV  # letters 0..15
for k, g in enumerate(LET):
    assert np.array_equal(g.T @ J.astype(np.int64) @ g, J.astype(np.int64)), ("not symplectic", k)
    assert np.array_equal(LET[k] @ LET[(k + 8) % 16], I4), ("inverse", k)
def inv_letter(k): return (k + 8) % 16

# ---------- BFS ----------
t0 = time.time()
key = lambda m: tuple(m.reshape(-1))
start = key(I4)
dist = {start: 0}
word = {start: ()}
mat = {start: I4}
frontier = deque([start])
relators = set()
def free_reduce(w):
    out = []
    for a in w:
        if out and out[-1] == inv_letter(a): out.pop()
        else: out.append(a)
    return tuple(out)
def cyc_reduce(w):
    w = list(free_reduce(w))
    while len(w) >= 2 and w[0] == inv_letter(w[-1]):
        w = w[1:-1]
    return tuple(w)
def canon(w):
    # canonical representative under cyclic rotation and inversion
    w = cyc_reduce(w)
    if not w: return w
    cands = []
    for ww in (w, tuple(inv_letter(a) for a in reversed(w))):
        for i in range(len(ww)):
            cands.append(ww[i:] + ww[:i])
    return min(cands)
n_edges = 0
while frontier:
    k = frontier.popleft()
    d = dist[k]
    if d >= L: continue
    m = mat[k]; w = word[k]
    for a in range(16):
        m2 = m @ LET[a]
        k2 = key(m2)
        if k2 not in dist:
            dist[k2] = d + 1; word[k2] = w + (a,); mat[k2] = m2
            frontier.append(k2)
        else:
            n_edges += 1
            w2 = word[k2]
            rel = w + (a,) + tuple(inv_letter(b) for b in reversed(w2))
            rel = canon(rel)
            if 0 < len(rel) <= LMAX:
                relators.add(rel)
print(f"BFS radius {L}: {len(dist)} elements, {n_edges} non-tree edges, {len(relators)} distinct relators (len<={LMAX}), {time.time()-t0:.1f}s", flush=True)

# ---------- verify relators in Sp_4(Z) ----------
def evalword(w):
    m = I4
    for a in w: m = m @ LET[a]
    return m
bad = [r for r in relators if not np.array_equal(evalword(r), I4)]
assert not bad, f"{len(bad)} relators fail"
print("all relators evaluate to identity in Sp_4(Z)", flush=True)

# ---------- winding lifts (vectorized) ----------
N_STACK = np.array([g.astype(float) - np.eye(4) for g in LET])  # letters: x_a(1) = I + N ; inverses: I - N
for a in range(16):
    assert np.allclose(N_STACK[a] @ N_STACK[a], 0), "not square-zero"
I4f = np.eye(4)
def polar_unitary_batch(G):
    s = np.transpose(G, (0, 2, 1)) @ G
    wv, V = np.linalg.eigh(s)
    sih = V @ (V.transpose(0, 2, 1) / np.sqrt(wv)[:, :, None])
    return G @ sih
def det_phase_batch(U):
    M = U[:, :2, :2] + 1j * U[:, :2, 2:]
    return np.angle(np.linalg.det(M))
def winding_batch(W, steps=32):
    n, ell = W.shape
    G = np.broadcast_to(I4f, (n, 4, 4)).copy()
    prev = det_phase_batch(polar_unitary_batch(G))
    total = np.zeros(n)
    for p in range(ell):
        Np = N_STACK[W[:, p]]                     # (n,4,4)
        for s in range(1, steps + 1):
            t = s / steps
            Gt = G @ (I4f + t * Np)
            ph = det_phase_batch(polar_unitary_batch(Gt))
            d = (ph - prev + np.pi) % (2 * np.pi) - np.pi
            total += d; prev = ph
        G = G @ (I4f + Np)
    return total / (2 * np.pi)
def winding(wrd, steps=32):
    return float(winding_batch(np.array([wrd], dtype=np.int64), steps)[0])

def w_of(a):
    return (a, inv_letter(a + 4), a)
for a, nm in [(0, "long 2e1"), (1, "long 2e2"), (2, "short e1+e2"), (3, "short e1-e2")]:
    w4 = w_of(a) * 4
    assert np.array_equal(evalword(w4), I4)
    print(f"winding of w_{nm}^4 = {winding(w4):.4f}", flush=True)

t1 = time.time()
rels = sorted(relators, key=lambda r: (len(r), r))
lifts = [0] * len(rels)
maxdev = 0.0
from collections import defaultdict
byl = defaultdict(list)
for i, r in enumerate(rels):
    if len(r) >= 12: byl[len(r)].append(i)
for ell, idxs in sorted(byl.items()):
    W = np.array([rels[i] for i in idxs], dtype=np.int64)
    for start in range(0, len(idxs), 20000):
        ks = winding_batch(W[start:start + 20000])
        for j, k in zip(idxs[start:start + 20000], ks):
            kr = int(np.rint(k)); maxdev = max(maxdev, abs(k - kr)); lifts[j] = kr
    print(f"  length {ell}: {len(idxs)} relators lifted, {time.time()-t1:.0f}s", flush=True)
print(f"computed lifts for {sum(len(v) for v in byl.values())} relators of length >= 12 (shorter ones lift trivially, verified at radius 5), max deviation from integer {maxdev:.2e}", flush=True)
from collections import Counter
print("lift exponent histogram (len>=12):", sorted(Counter(lifts[i] for v in byl.values() for i in v).items()), flush=True)
print("nonzero-lift relators:", sum(1 for k in lifts if k != 0), flush=True)
json.dump({"letters": 16, "root_names": [n for n, _ in roots], "relators": [list(r) for r in rels], "lifts": lifts,
           "generators": [g.tolist() for g in GEN]}, open(OUT, "w"))
print("wrote", OUT, flush=True)
