import json, numpy as np
exec(open("theta_seed.py").read().split("# scalarity check on a sample")[0])
M16 = np.concatenate([rho, np.conj(np.transpose(rho, (0,2,1)))])
def expsum(r):
    n = [0]*8
    for a in r: n[a % 8] += 1 if a < 8 else -1
    return n
phases = []; bad = 0
for r in rels:
    P = np.eye(4, dtype=complex)
    for a in r: P = P @ M16[a]
    l = P[0,0]
    if not np.allclose(P, l*np.eye(4), atol=1e-8): bad += 1; phases.append(None)
    else: phases.append(int(round(np.angle(l)/np.pi)) % 2)   # 0 -> +1, 1 -> -1
print(f"nonscalar relators: {bad} of {len(rels)}", flush=True)
# can the seed be rescaled to a genuine representation (all +1)?  solve eps over F2: n_r . x = log(lam_r)
rows = [[x % 2 for x in expsum(r)] for r in rels]; rhs = phases
Ab = np.concatenate([np.array(rows, dtype=np.int64), np.array(rhs, dtype=np.int64)[:, None]], axis=1) % 2
r0 = 0; piv = []
for c in range(8):
    sel = [i for i in range(r0, Ab.shape[0]) if Ab[i, c] == 1]
    if not sel: continue
    Ab[[r0, sel[0]]] = Ab[[sel[0], r0]]
    for i in range(Ab.shape[0]):
        if i != r0 and Ab[i, c] == 1: Ab[i] ^= Ab[r0]
    piv.append(c); r0 += 1
inconsistent = any(Ab[i, :8].sum() == 0 and Ab[i, 8] == 1 for i in range(Ab.shape[0]))
print("seed rescalable to a genuine representation of Sp_4(Z):", not inconsistent, flush=True)
from collections import Counter
print("phase pattern over relators (0 = +I, 1 = -I):", Counter(phases), flush=True)
print("phases on the 20 lifted relators:", [phases[i] for i,k in enumerate(lifts) if k != 0], flush=True)
json.dump({"phases": phases}, open("spin_phases.json", "w"))
json.dump({"seed": [[[float(z.real), float(z.imag)] for z in row] for U in rho for row in U], "d": 4}, open("seed_spin_d4.json", "w"))
print("wrote spin_phases.json and seed_spin_d4.json", flush=True)
