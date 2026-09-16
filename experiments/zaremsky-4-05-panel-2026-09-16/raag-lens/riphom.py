"""Independent homology check of Vietoris-Rips complexes VR_t(K) (closed: diam <= t)
for finite convex subgraphs K of 2-dim median graphs (RAAG Cayley graphs, boxes).
Uses the compiled pyRipser backend (PYTHONPATH must contain the scratchpad pylib).
Gate projection onto a convex K is 1-Lipschitz, so H_*(VR_t(K)) is a direct summand of
H_*(VR_t(G)); nonzero reduced homology of VR_t(K) is nonzero homology of VR_t(G)."""
import sys, itertools, time
import numpy as np
import pyRipser

def vr_betti(D, t, maxdim=2, coeff=2):
    n = D.shape[0]
    r, c = np.meshgrid(np.arange(n), np.arange(n))
    DP = np.array(D[r > c], dtype=np.float32)
    res = pyRipser.doRipsFiltrationDM(DP, maxdim, float(t) + 0.25, coeff, False)
    dg = res["births_and_deaths_by_dim"]
    out = []
    for d in range(len(dg)):
        a = np.reshape(np.array(dg[d]), [-1, 2])
        inf = int(np.sum(np.isinf(a[:, 1])))
        out.append(inf - (1 if d == 0 else 0))
    return out  # reduced Betti numbers of VR_t, dims 0..maxdim

def selftest():
    # square C4 (l1 unit square): VR_1 = 4-cycle -> b1=1; VR_2 = simplex
    pts = [(0,0),(1,0),(1,1),(0,1)]
    D = np.array([[abs(a[0]-b[0])+abs(a[1]-b[1]) for b in pts] for a in pts], float)
    print("C4 t=1", vr_betti(D, 1), "expect [0,1,0]")
    print("C4 t=2", vr_betti(D, 2), "expect [0,0,0]")
    # 6-cycle graph metric: VR_1 = hexagon b1=1, VR_2 = octahedron-ish? known: VR_2(C6) ~ S^2
    n=6
    D = np.array([[min(abs(i-j), n-abs(i-j)) for j in range(n)] for i in range(n)], float)
    print("C6 t=1", vr_betti(D, 1), "expect [0,1,0]")
    print("C6 t=2", vr_betti(D, 2), "expect [0,0,1] (octahedron S^2)")
    # C5 t=2 -> simplex
    n=8
    D = np.array([[min(abs(i-j), n-abs(i-j)) for j in range(n)] for i in range(n)], float)
    print("C8 t=2", vr_betti(D, 2, maxdim=3), "expect S^3 [0,0,0,1]")

if __name__ == "__main__":
    selftest()
