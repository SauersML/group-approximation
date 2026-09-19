import json, sys, numpy as np
pres = json.load(open("pres6.json")); rels = pres["relators"]; lifts = np.array(pres["lifts"])
U = np.load(sys.argv[1]); d = U.shape[1]; m = int(sys.argv[2])
M = np.concatenate([U, np.conj(np.transpose(U, (0,2,1)))])
byl = {}
for i, r in enumerate(rels): byl.setdefault(len(r), []).append(i)
mx = 0.0; mxl = 0.0; tot = 0.0
for ell, idx in sorted(byl.items()):
    W = np.array([rels[i] for i in idx]); n = len(idx)
    P = np.broadcast_to(np.eye(d, dtype=complex), (n, d, d)).copy()
    for p in range(ell): P = P @ M[W[:, p]]
    c = np.exp(2j*np.pi*(lifts[idx] % m)/m)
    D = P - c[:, None, None]*np.eye(d)
    sq = np.real(np.einsum('nij,nij->n', np.conj(D), D))/d
    tot += sq.sum(); mx = max(mx, float(np.sqrt(sq.max())))
    lifted = (lifts[idx] % m) != 0
    if lifted.any(): mxl = max(mxl, float(np.sqrt(sq[lifted].max())))
print(f"{sys.argv[1]} sector mod {m}: over ALL {len(rels)} relators: mean sq defect {tot/len(rels):.6f}, max defect {mx:.4f}, max lifted defect {mxl:.4f}", flush=True)
