import itertools
import numpy as np
from pysat.solvers import Glucose4, Cadical153

def partitions(k):
    def rec(i, cur, mx):
        if i == k:
            yield tuple(cur); return
        for c in range(mx+1):
            cur.append(c)
            yield from rec(i+1, cur, mx+1 if c == mx else mx)
            cur.pop()
    yield from rec(0, [], 0)

def build(nS, nM, Tf, Tr, n):
    # variable layout: mu[x][a] -> 1 + x*n + a ; nu[y][a] -> 1 + n^nM*n + y*n + a ; e_q after
    NM = n**nM; NSs = n**nS
    muv = lambda x, a: 1 + x*n + a
    base_nu = 1 + NM*n
    clauses = []
    # exactly one
    for x in range(NM):
        clauses.append([muv(x,a) for a in range(n)])
        for a in range(n):
            for b in range(a+1, n):
                clauses.append([-muv(x,a), -muv(x,b)])
    for y in range(NSs):
        clauses.append([base_nu + y*n + a for a in range(n)])
        for a in range(n):
            for b in range(a+1, n):
                clauses.append([-(base_nu+y*n+a), -(base_nu+y*n+b)])
    powM = n ** np.arange(nM-1, -1, -1)
    powS = n ** np.arange(nS-1, -1, -1)
    ncf = max(Tf)+1
    asg = np.array(list(itertools.product(range(n), repeat=ncf)), dtype=np.int64)  # P x ncf
    Tf_arr = np.array(Tf).reshape(nS, nM)
    rows = asg[:, Tf_arr]  # P x nS x nM
    rowidx = rows @ powM   # P x nS
    p11 = asg[:, Tf[0]]
    ys = np.array(list(itertools.product(range(n), repeat=nS)), dtype=np.int64)  # Y x nS
    yidx = ys @ powS
    # clause: -mu[rowidx[p,s], ys[y,s]] for s, + nu[yidx[y], p11[p]]
    P = asg.shape[0]; Y = ys.shape[0]
    lit_mu = -(1 + rowidx[:, None, :]*n + ys[None, :, :])  # P x Y x nS
    lit_nu = (base_nu + yidx[None, :]*n + p11[:, None])    # P x Y
    dec = np.concatenate([lit_mu, lit_nu[:, :, None]], axis=2).reshape(P*Y, nS+1)
    clauses.extend(dec.tolist())
    # not Enc
    ncr = max(Tr)+1
    asgr = np.array([a for a in itertools.product(range(n), repeat=ncr) if a[Tr[0]] == 0], dtype=np.int64)
    Q = asgr.shape[0]
    Tr_arr = np.array(Tr).reshape(nM, nS)
    rrows = asgr[:, Tr_arr]  # Q x nM x nS
    rridx = rrows @ powS     # Q x nM
    zs = np.array(list(itertools.product(range(n), repeat=nM)), dtype=np.int64)  # Z x nM
    zidx = zs @ powM
    base_e = base_nu + NSs*n
    evars = base_e + np.arange(Q)
    Zn = zs.shape[0]
    lit_e = -np.broadcast_to(evars[:, None, None], (Q, Zn, 1))
    lit_nu2 = -(base_nu + rridx[:, None, :]*n + zs[None, :, :])  # Q x Z x nM
    lit_mu2 = -np.broadcast_to((1 + zidx*n + 0)[None, :, None], (Q, Zn, 1))
    enc = np.concatenate([lit_e, lit_nu2, lit_mu2], axis=2).reshape(Q*Zn, nM+2)
    clauses.extend(enc.tolist())
    clauses.append(evars.tolist())
    return clauses, base_nu, NM, NSs

def solve(nS, nM, Tf, Tr, n, budget=None, model=False):
    clauses, base_nu, NM, NSs = build(nS, nM, Tf, Tr, n)
    with Cadical153(bootstrap_with=clauses) as s:
        if budget is None:
            ok = s.solve()
        else:
            s.conf_budget(budget)
            ok = s.solve_limited()
        if ok and model:
            mdl = set(l for l in s.get_model() if l > 0)
            mu = [next(a for a in range(n) if 1+x*n+a in mdl) for x in range(NM)]
            nu = [next(a for a in range(n) if base_nu+y*n+a in mdl) for y in range(NSs)]
            return True, mu, nu
        return ok, None, None
