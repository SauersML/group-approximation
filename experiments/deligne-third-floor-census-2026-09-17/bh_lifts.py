"""Birman-Hilden presentation of Sp_4(Z) = Mod(S_2)/<<(a1a2)^6>> on symplectic
transvections a_i = T_{v_i}, and universal-cover lift exponents k_r of each relator,
computed as the winding of arg det(A+iC) of the polar-unitary part along the
straight paths I + t N_v (t in [0,1]) concatenated.  k_r in Z = pi_1(Sp_4(R)).

Usage: python3 bh_lifts.py OUT.json
"""
import numpy as np, json, sys

# symplectic form on basis e1,e2,f1,f2 ; w(e_i,f_j)=delta_ij
J = np.array([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]])
def om(x, y): return int(x @ J @ y)
e1, e2, f1, f2 = np.eye(4, dtype=int)
V = [e1, f1, e2 - e1, f2, e2]  # chain c1..c5
for i in range(5):
    for j in range(5):
        if abs(i - j) == 1: assert abs(om(V[i], V[j])) == 1
        elif i != j: assert om(V[i], V[j]) == 0

def N_of(v):  # T_v x = x + w(x,v) v
    N = np.zeros((4, 4), dtype=int)
    for k in range(4):
        x = np.eye(4, dtype=int)[k]
        N[:, k] = om(x, v) * v
    return N
NS = [N_of(v) for v in V]
GEN = [np.eye(4, dtype=int) + N for N in NS]
for g in GEN: assert np.array_equal(g.T @ J @ g, J)

def lett(a): return GEN[a] if a < 5 else (np.eye(4, dtype=int) - NS[a - 5])
def inv(a): return (a + 5) % 10
def winv(word): return [inv(a) for a in reversed(word)]

def relators():
    R = {}
    for i in range(4):
        R[f"braid{i+1}{i+2}"] = [i, i + 1, i, inv(i + 1), inv(i), inv(i + 1)]
    for i in range(5):
        for j in range(i + 2, 5):
            R[f"comm{i+1}{j+1}"] = [i, j, inv(i), inv(j)]
    R["chain6"] = [0, 1, 2, 3, 4] * 6
    iota = [0, 1, 2, 3, 4, 4, 3, 2, 1, 0]
    R["iota2"] = iota * 2
    R["iota_a1"] = iota + [0] + winv(iota) + [inv(0)]
    R["sep"] = [0, 1] * 6
    return R

def ev(word):
    m = np.eye(4, dtype=int)
    for x in word: m = m @ lett(x)
    return m

def phase(G):
    s = G.T @ G
    wv, U = np.linalg.eigh(s)
    P = G @ (U @ np.diag(wv ** -0.5) @ U.T)
    return np.angle(np.linalg.det(P[:2, :2] + 1j * P[:2, 2:]))

def winding(word, steps=200):
    G = np.eye(4); prev = phase(G); tot = 0.0
    for x in word:
        N = NS[x] if x < 5 else -NS[x - 5]
        for s in range(1, steps + 1):
            ph = phase(G @ (np.eye(4) + s / steps * N))
            d = (ph - prev + np.pi) % (2 * np.pi) - np.pi
            tot += d; prev = ph
        G = G @ (np.eye(4) + N)
    return tot / (2 * np.pi)

if __name__ == "__main__":
    R = relators()
    for k, r in R.items(): assert np.array_equal(ev(r), np.eye(4, dtype=int)), k
    out = {}
    for k, r in R.items():
        wd = winding(r); es = sum(1 if x < 5 else -1 for x in r)
        out[k] = dict(word=r, lift=int(round(wd)), dev=abs(wd - round(wd)), expsum=es)
        print(f"{k:10s} len={len(r):3d} expsum={es:3d} winding={wd:+.6f}")
    json.dump(out, open(sys.argv[1] if len(sys.argv) > 1 else "bh_relators.json", "w"), indent=1)
