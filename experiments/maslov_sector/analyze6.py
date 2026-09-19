"""Analyze a v6 best tuple: defects over ALL relators (mod 3), spectrum of the worst relator products, and,
when a seed is given, the per-generator phase relative to the seed after the best global unitary alignment and
the residual after removing that phase (residual ~ 0 means a pure coboundary rescaling; large means nonabelian)."""
import json, sys, numpy as np
pres = json.load(open("pres6.json")); rels = pres["relators"]; lifts = np.array(pres["lifts"])
U = np.load(sys.argv[1]); d = U.shape[1]; m = 3
seedfn = sys.argv[2] if len(sys.argv) > 2 else "none"
print("file", sys.argv[1], "dim", d)
print("generator |tr|/d:", np.round([abs(np.trace(U[i]))/d for i in range(8)], 3).tolist())
print("generator det phases /2pi:", np.round([np.angle(np.linalg.det(U[i]))/(2*np.pi) for i in range(8)], 3).tolist())
if seedfn != "none":
    J = json.load(open(seedfn)); a = np.array(J["seed"]); S = (a[:,:,0]+1j*a[:,:,1]).reshape(8, J["d"], J["d"])
    if S.shape[1] != d:
        k = d // S.shape[1]; S = np.stack([np.kron(S[i], np.eye(k)) for i in range(8)])
    A = sum(S[i] @ U[i].conj().T for i in range(8)); W, _, Vh = np.linalg.svd(A); Q = W @ Vh
    V = np.stack([Q @ U[i] @ Q.conj().T for i in range(8)])
    ph = np.array([np.angle(np.trace(S[i].conj().T @ V[i])) for i in range(8)])
    print("distance from seed per generator (aligned):", np.round([np.linalg.norm(V[i]-S[i])/np.sqrt(d) for i in range(8)], 4).tolist())
    print("phase relative to seed /2pi:", np.round(ph/(2*np.pi), 4).tolist())
    print("residual after removing the phase (nonabelian part):", np.round([np.linalg.norm(np.exp(-1j*ph[i])*V[i] - S[i])/np.sqrt(d) for i in range(8)], 4).tolist())
M = np.concatenate([U, np.conj(np.transpose(U, (0,2,1)))])
byl = {}
for i, r in enumerate(rels): byl.setdefault(len(r), []).append(i)
defs = np.zeros(len(rels)); keep = {}
for ell, idx in sorted(byl.items()):
    W_ = np.array([rels[i] for i in idx]); n = len(idx)
    P = np.broadcast_to(np.eye(d, dtype=complex), (n, d, d)).copy()
    for p in range(ell): P = P @ M[W_[:, p]]
    c = np.exp(2j*np.pi*(lifts[idx] % m)/m)
    D = P - c[:, None, None]*np.eye(d)
    sq = np.real(np.einsum('nij,nij->n', np.conj(D), D))/d
    defs[idx] = np.sqrt(sq)
    top = np.argsort(-sq)[:3]
    for j in top: keep[idx[j]] = P[j]
lifted = (lifts % m) != 0
print(f"ALL relators: mean sq {np.mean(defs**2):.6f}, max defect {defs.max():.4f}, max lifted {defs[lifted].max():.4f}, max unlifted {defs[~lifted].max():.4f}")
print("count > 0.5:", int((defs > 0.5).sum()), " > 0.3:", int((defs > 0.3).sum()), " > 0.2:", int((defs > 0.2).sum()), " > 0.1:", int((defs > 0.1).sum()))
order = np.argsort(-defs)[:6]
for i in order:
    if i in keep:
        ev = np.sort(np.angle(np.linalg.eigvals(keep[i]))/(2*np.pi))
        print(f"  rel {i} len {len(rels[i])} lift {lifts[i]} defect {defs[i]:.4f} target/2pi {(lifts[i]%3)/3:.3f} eigenphases/2pi {np.round(ev,3).tolist()}")
