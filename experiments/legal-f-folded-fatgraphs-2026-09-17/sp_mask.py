"""Support propagation (arc consistency) for the memory-r word-free polygon LP of lp_memory.py.

A slot d -> q is *supported* if it lies on some legal typed polygon all of whose slots are supported, its
reverse q -> d is supported (pair balance), and both windows of d and q may carry flow.  A window may carry
flow only if every type of it lies on a supported slot and its r-path edge lies on a cycle of such windows.
Anything unsupported is zero in every feasible point of the LP, so removing it is exact.  If nothing
survives, the LP is infeasible, and no legal f^m-folded fatgraph exists at all.

usage: python3 support_propagation_memory.py '<phi0 json>' m r [--maxval K]
"""
import sys, json, itertools
import numpy as np
import lp_memory as LM
import lp_allwords as LA
from ffold import inv


def scc_edges(nodes_edges):
    """nodes_edges: list of (u, v) edges; return set of indices of edges inside a strongly connected comp."""
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import connected_components
    nodes = sorted({u for u, v in nodes_edges} | {v for u, v in nodes_edges})
    ni = {x: k for k, x in enumerate(nodes)}
    A = coo_matrix((np.ones(len(nodes_edges)), ([ni[u] for u, v in nodes_edges], [ni[v] for u, v in nodes_edges])),
                   shape=(len(nodes), len(nodes)))
    _, lab = connected_components(A, directed=True, connection="strong")
    comp = {x: lab[ni[x]] for x in nodes}
    return {i for i, (u, v) in enumerate(nodes_edges) if comp[u] == comp[v]}


def propagate(TY, g, maxval, log=print, wmask=None):
    N = TY.N
    LET = TY.L
    gl = sorted({g[x] for x in LET})
    gid = np.array([gl.index(g[TY.label[d]]) for d in range(N)])
    mk = np.array([k == "-" for k in TY.kind])
    fd = np.array(TY.fdart, dtype=bool)
    li = np.array([LET.index(x) for x in TY.label])
    invi = np.array([LET.index(inv(x)) for x in LET])
    S = (li[None, :] == invi[li][:, None]) & ~(mk[:, None] & mk[None, :])
    SU = np.zeros((N, N), dtype=np.float32)
    for q in range(N):
        for n in TY.succ[q]:
            SU[q, n] = 1.0
    cw = np.array(TY.cw)
    W = TY.windows
    walive = np.ones(len(W), dtype=bool) if wmask is None else np.array(wmask, dtype=bool)
    blocks = {}
    for gi in range(len(gl)):
        for m in (False, True):
            idx = np.where((gid == gi) & (mk == m) & ~fd)[0]
            if len(idx):
                blocks[(gi, m)] = idx
    ok2 = (gid[:, None] != gid[None, :]) & ~(mk[:, None] & mk[None, :]) & ~(fd[:, None] & fd[None, :])
    it = 0
    while True:
        it += 1
        talive = walive[cw]
        S &= talive[:, None] & talive[None, :]
        # C[d, n]: some supported slot d -> q with n in succ(q), n alive
        C = (S.astype(np.float32) @ SU) > 0
        C &= talive[None, :]
        E = C & C.T & ok2                     # edges on 2-gons
        Cf = C.astype(np.float32)
        keys = list(blocks)
        for kk in (3, 4):
            if kk > maxval:
                continue
            for seq in itertools.permutations(keys, kk):
                gs = [s[0] for s in seq]
                if len(set(gs)) < kk or sum(s[1] for s in seq) > 1:
                    continue
                I = [blocks[s] for s in seq]
                # path back from I[1] to I[0] through I[2..]
                P = Cf[np.ix_(I[1], I[2])]
                for j in range(2, kk - 1):
                    P = ((P @ Cf[np.ix_(I[j], I[j + 1])]) > 0).astype(np.float32)
                P = (P @ Cf[np.ix_(I[kk - 1], I[0])]) > 0          # (n in I1, d in I0)
                sub = C[np.ix_(I[0], I[1])] & P.T
                E[np.ix_(I[0], I[1])] |= sub
        # slot d->q supported iff exists n in succ(q) with E[d, n]
        Sn = S & ((E.astype(np.float32) @ SU.T) > 0)
        Sn &= Sn.T
        tsup = Sn.any(axis=1)
        wn = walive.copy()
        for i in np.where(~tsup & talive)[0]:
            wn[cw[i]] = False
        # circulation support
        idx = [j for j in range(len(W)) if wn[j]]
        if idx:
            inscc = scc_edges([(W[j][:-1], W[j][1:]) for j in idx])
            for k, j in enumerate(idx):
                if k not in inscc:
                    wn[j] = False
        changed = (wn != walive).any() or (Sn != S).any()
        log("ac it", it, "windows", int(wn.sum()), "types", int(wn[cw].sum()), "slots", int(Sn.sum()),
            flush=True)
        S, walive = Sn, wn
        if not changed or not walive.any():
            break
    return walive, S


def homology_feasible(TY, walive):
    """Is there a nonnegative circulation on the surviving windows with zero homology and total 1?"""
    from scipy.optimize import linprog
    W = [v for j, v in enumerate(TY.windows) if walive[j]]
    if not W:
        return False
    pre = sorted({v[:-1] for v in W} | {v[1:] for v in W})
    pi = {s: k for k, s in enumerate(pre)}
    letters = sorted(TY.phi)
    A = np.zeros((len(pre) + len(letters) + 1, len(W)))
    for j, v in enumerate(W):
        A[pi[v[:-1]], j] += 1; A[pi[v[1:]], j] -= 1
        x = v[0]; A[len(pre) + letters.index(x.lower()), j] += 1 if x.islower() else -1
        A[-1, j] = 1
    b = np.zeros(A.shape[0]); b[-1] = 1
    res = linprog(np.zeros(len(W)), A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    return res.status == 0


def main():
    args = sys.argv[1:]
    maxval = None
    if "--maxval" in args:
        i = args.index("--maxval"); maxval = int(args[i + 1]); del args[i:i + 2]
    phi0 = json.loads(args[0]); m = int(args[1]); r = int(args[2])
    phi = LA.power(phi0, m)
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    if maxval is None:
        maxval = max(2, 2 * min(gp, gn))
    TY = LM.MTypes(phi, g, r)
    print("phi0", phi0, "m", m, "r", r, "windows", len(TY.windows), "types", TY.N, "maxval", maxval, flush=True)
    walive, S = propagate(TY, g, maxval)
    hf = homology_feasible(TY, walive)
    print("surviving windows", ["".join(v) for j, v in enumerate(TY.windows) if walive[j]])
    print("RESULT", "empty" if not walive.any() else ("homology-infeasible" if not hf else "survives"),
          int(walive.sum()), flush=True)


if __name__ == "__main__":
    main()
