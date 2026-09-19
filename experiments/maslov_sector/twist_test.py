import json, numpy as np
exec(open("theta_seed.py").read().split("# scalarity check on a sample")[0])
def expsum(r):
    n = [0]*8
    for a in r: n[a % 8] += 1 if a < 8 else -1
    return n
def parity(p):
    seen=[False]*6; sgn=0
    for i in range(6):
        if seen[i]: continue
        j=i; c=0
        while not seen[j]: seen[j]=True; j=p[j]; c+=1
        sgn += c-1
    return sgn % 2
sgn = [parity(p) for p in perm]
print("parities of generator permutations:", sgn, flush=True)
lifted_idx = [i for i,k in enumerate(lifts) if k != 0]
rng = np.random.default_rng(3)
sample = lifted_idx + list(rng.choice(len(rels), size=20000, replace=False))
def scalars(R8):
    M = np.concatenate([R8, np.conj(np.transpose(R8,(0,2,1)))])
    out = {}
    for i in sample:
        P = np.eye(4, dtype=complex)
        for a in rels[i]: P = P @ M[a]
        l = P[0,0]
        assert np.allclose(P, l*np.eye(4), atol=1e-8), "nonscalar"
        out[i] = l
    return out
def solve(lam, target):  # find eps in {+-1}^8 with eps^{n_r} lam_r = target_r (all +-1)
    rows=[]; rhs=[]
    for i,l in lam.items():
        lg = 0 if abs(l-1)<1e-6 else (1 if abs(l+1)<1e-6 else None)
        assert lg is not None, "phase not +-1"
        rows.append([x%2 for x in expsum(rels[i])]); rhs.append((lg + target(i)) % 2)
    Ab = np.concatenate([np.array(rows,dtype=np.int64), np.array(rhs,dtype=np.int64)[:,None]],axis=1)%2
    r=0
    for c in range(8):
        sel=[i for i in range(r,Ab.shape[0]) if Ab[i,c]==1]
        if not sel: continue
        Ab[[r,sel[0]]]=Ab[[sel[0],r]]
        for i in range(Ab.shape[0]):
            if i!=r and Ab[i,c]==1: Ab[i]^=Ab[r]
        r+=1
    return not any(Ab[i,:8].sum()==0 and Ab[i,8]==1 for i in range(Ab.shape[0]))
for name, R8 in [("spin", rho), ("spin twisted by i^sign", np.stack([(1j**sgn[k])*rho[k] for k in range(8)])), ("i^sign alone (scalar rep)", np.stack([(1j**sgn[k])*np.eye(4) for k in range(8)]))]:
    lam = scalars(R8)
    phases = sorted(set(np.round(np.angle(l)/np.pi,3) for l in lam.values()))
    ok_triv = solve(lam, lambda i: 0); ok_meta = solve(lam, lambda i: lifts[i] % 2)
    print(f"{name}: scalar phases/pi {phases}; rescalable to genuine: {ok_triv}; matches metaplectic lift pattern: {ok_meta}", flush=True)
