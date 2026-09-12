"""Analyze a saved best tuple against the exact metaplectic theta seed:
distance from the seed, worst relators over ALL relators, structure of rho(r) on the worst ones."""
import json, sys, numpy as np
pres = json.load(open("pres6.json")); rels = pres["relators"]; lifts = np.array(pres["lifts"]); gens = pres.get("generators")
U = np.load(sys.argv[1]); d = U.shape[1]; m = int(sys.argv[2])
J = json.load(open(sys.argv[3])); a = np.array(J["seed"]); S = (a[:,:,0]+1j*a[:,:,1]).reshape(8, J["d"], J["d"])
if S.shape[1] != d:
    k = d // S.shape[1]; S = np.stack([np.kron(S[i], np.eye(k)) for i in range(8)])
print("dim", d, "sector mod", m)
print("normalized-HS distance of each generator from the seed:", np.round([np.linalg.norm(U[i]-S[i])/np.sqrt(d) for i in range(8)], 4))
print("generator normalized traces |tr|/d:", np.round([abs(np.trace(U[i]))/d for i in range(8)], 4))
# best unitary conjugation aligning U to S? (Procrustes on the direct sum)
A = sum(S[i] @ U[i].conj().T for i in range(8)); W, _, Vh = np.linalg.svd(A); Q = W @ Vh
print("after best global unitary alignment, distances:", np.round([np.linalg.norm(Q @ U[i] @ Q.conj().T - S[i])/np.sqrt(d) for i in range(8)], 4))
M = np.concatenate([U, np.conj(np.transpose(U, (0,2,1)))])
byl = {}
for i, r in enumerate(rels): byl.setdefault(len(r), []).append(i)
defs = np.zeros(len(rels)); P_all = {}
for ell, idx in sorted(byl.items()):
    W_ = np.array([rels[i] for i in idx]); n = len(idx)
    P = np.broadcast_to(np.eye(d, dtype=complex), (n, d, d)).copy()
    for p in range(ell): P = P @ M[W_[:, p]]
    c = np.exp(2j*np.pi*(lifts[idx] % m)/m)
    D = P - c[:, None, None]*np.eye(d)
    sq = np.real(np.einsum('nij,nij->n', np.conj(D), D))/d
    defs[idx] = np.sqrt(sq)
    for j, i in enumerate(idx):
        if sq[j] > 0.04: P_all[i] = P[j]
order = np.argsort(-defs)
print("relators with defect > 0.2:", int((defs > 0.2).sum()), " > 0.1:", int((defs > 0.1).sum()), " > 0.05:", int((defs > 0.05).sum()), "of", len(rels))
print("histogram of defects (edges 0,.02,.05,.1,.2,.3,.4,.5):", np.histogram(defs, bins=[0,.02,.05,.1,.2,.3,.4,.5,10])[0])
for i in order[:12]:
    ev = np.linalg.eigvals(P_all[i])
    print(f"rel {i} len {len(rels[i])} lift {lifts[i]} word {rels[i]} defect {defs[i]:.4f} eigenphases/2pi {np.round(np.sort(np.angle(ev)/(2*np.pi)),3)}")
# which generators appear in the bad relators
from collections import Counter
cnt = Counter(); 
for i in order[:200]:
    for x in rels[i]: cnt[x % 8] += 1
print("letter counts in the 200 worst relators (generator index mod 8):", sorted(cnt.items()))
