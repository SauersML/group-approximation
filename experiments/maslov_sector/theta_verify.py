import json, numpy as np, itertools
pres = json.load(open("pres6.json")); rels = pres["relators"]; lifts = pres["lifts"]
R8 = np.load("theta10_generators.npy"); M = np.concatenate([R8, np.conj(np.transpose(R8, (0,2,1)))])
# level: smallest N with rho(x_alpha)^N scalar
for a in range(8):
    U = R8[a]; P = np.eye(10, dtype=complex); orders = []
    for n in range(1, 17):
        P = P @ U
        if np.allclose(P, P[0,0]*np.eye(10), atol=1e-8): orders.append(n); break
    print(f"generator {a}: rho(x)^N scalar first at N = {orders}", flush=True)
bad = 0; mism = 0
byl = {}
for i, r in enumerate(rels): byl.setdefault(len(r), []).append(i)
for ell, idx in sorted(byl.items()):
    W = np.array([rels[i] for i in idx]); n = len(idx)
    P = np.broadcast_to(np.eye(10, dtype=complex), (n, 10, 10)).copy()
    for p in range(ell): P = P @ M[W[:, p]]
    d = P - P[:, 0, 0][:, None, None] * np.eye(10)
    ns = np.linalg.norm(d.reshape(n, -1), axis=1) > 1e-6
    bad += int(ns.sum())
    ph = np.angle(P[:, 0, 0]); K = np.array([lifts[i] for i in idx])
    expected = np.pi * (K % 2)
    mism += int((np.abs(np.exp(1j*ph) - np.exp(1j*expected)) > 1e-6).sum())
print(f"all {len(rels)} relators: nonscalar {bad}, phase mismatches with (-1)^k: {mism}", flush=True)
