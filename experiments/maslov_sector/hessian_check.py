"""Second-order analysis at an exact metaplectic model for the mod-3 mean-square relator energy.
Chart: U_s exp(i sum_k t_k H_k) with H_k an orthonormal basis of Hermitian d x d matrices for each generator
(identity direction = coboundary, the rest traceless).  Hessian of E o chart at t = 0 by central differences of
function values (polarization), eigenvalues of the traceless block and of its Schur complement against the
coboundary block; saves the most negative traceless directions if any.
usage: hessian_check.py SEED.json d n_unl h"""
import sys, json, numpy as np
seedfn = sys.argv[1]; dd = int(sys.argv[2]); n_unl = int(sys.argv[3]); h = float(sys.argv[4])
src = open("optimize6.py").read().split("best = None")[0]
sys.argv = ["optimize6.py", "pres6.json", "3", "seed:" + seedfn, str(dd), "1", "0", str(n_unl), "5", "1", "0", "0.0"]
exec(src)
U0 = load_seed(seedfn); CU = classes_of(z, maxlen=13)
def E_of(Us): return energy_and_grad(Us, CU)[0]
# orthonormal Hermitian basis: identity/sqrt(d), then traceless
basis = [np.eye(d)/np.sqrt(d)]
for i in range(d):
    for j in range(i+1, d):
        A = np.zeros((d,d), dtype=complex); A[i,j] = 1; A[j,i] = 1; basis.append(A/np.sqrt(2))
        B = np.zeros((d,d), dtype=complex); B[i,j] = -1j; B[j,i] = 1j; basis.append(B/np.sqrt(2))
for i in range(1, d):
    Dg = np.zeros(d); Dg[:i] = 1; Dg[i] = -i; basis.append(np.diag(Dg)/np.linalg.norm(Dg))
assert len(basis) == d*d
dirs = [(s, k) for s in range(8) for k in range(d*d)]   # index -> (generator, basis element)
n = len(dirs)
def point(tvec):
    Us = U0.copy()
    for s in range(8):
        A = sum(tvec[s*d*d + k] * basis[k] for k in range(d*d) if tvec[s*d*d + k] != 0)
        if np.any(A): Us[s] = U0[s] @ expiH(A)
    return Us
E0 = E_of(U0)
print(f"seed {seedfn} d={d} relators in working set {sum(W.shape[0] for _,W,_ in CU) + sum(W.shape[0] for _,W,_ in CL)} E0={E0:.6e} h={h}", flush=True)
# gradient by central differences (check of the criticality claim in this chart)
g = np.zeros(n)
for a in range(n):
    e = np.zeros(n); e[a] = h
    g[a] = (E_of(point(e)) - E_of(point(-e))) / (2*h)
cob = [s*d*d for s in range(8)]; trl = [a for a in range(n) if a not in cob]
print("gradient: max |traceless| %.3e, coboundary components %s" % (np.abs(g[trl]).max(), np.round(g[cob], 5).tolist()), flush=True)
# Hessian by polarization; exploit symmetry
Hm = np.zeros((n, n)); cache = {}
def Ept(vec):
    key = tuple(np.round(vec/h).astype(int)); 
    if key not in cache: cache[key] = E_of(point(vec))
    return cache[key]
for a in range(n):
    ea = np.zeros(n); ea[a] = h
    Hm[a, a] = (Ept(ea) - 2*E0 + Ept(-ea)) / (h*h)
    for b in range(a+1, n):
        eb = np.zeros(n); eb[b] = h
        Hm[a, b] = Hm[b, a] = (Ept(ea+eb) - Ept(ea-eb) - Ept(-ea+eb) + Ept(-ea-eb)) / (4*h*h)
    if a % 20 == 0: print(f"  row {a}/{n} done", flush=True)
Ht = Hm[np.ix_(trl, trl)]; Hc = Hm[np.ix_(cob, cob)]; Htc = Hm[np.ix_(trl, cob)]
wt = np.linalg.eigvalsh(Ht)
print("traceless block: eigenvalues min %.4e, number < -1e-6: %d, number < 1e-8: %d of %d; max %.4e" % (wt.min(), int((wt < -1e-6).sum()), int((wt < 1e-8).sum()), len(wt), wt.max()), flush=True)
print("smallest ten:", np.round(wt[:10], 6).tolist(), flush=True)
wc = np.linalg.eigvalsh(Hc); print("coboundary block eigenvalues:", np.round(wc, 6).tolist(), flush=True)
S = Ht - Htc @ np.linalg.pinv(Hc) @ Htc.T; ws = np.linalg.eigvalsh(S)
print("Schur complement (traceless after optimizing the coboundary): min %.4e, number < -1e-6: %d; smallest five %s" % (ws.min(), int((ws < -1e-6).sum()), np.round(ws[:5], 6).tolist()), flush=True)
wv, V = np.linalg.eigh(Ht)
np.save(f"hess_{seedfn}_traceless_eigvals.npy", wv); np.save(f"hess_{seedfn}_traceless_eigvecs.npy", V[:, :5])
np.save(f"hess_{seedfn}_full.npy", Hm)
print("saved", flush=True)
