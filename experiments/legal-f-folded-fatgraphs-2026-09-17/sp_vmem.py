"""Support propagation (exact arc consistency, as sp_mask.py) for the mixed-memory LP of lp_vmem.py.
A type is alive iff one of the windows counting it (VTypes.tw) is alive; a type on no supported slot kills
all of its windows.  Everything removed is zero in every feasible point, so an empty result means infeasible.
usage: python3 sp_vmem.py '<phi0 json>' m rm rp [MASKLETTERS]
"""
import sys, json, itertools
import numpy as np
import lp_vmem as VM
from ffold import inv
from sp_mask import scc_edges


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
    tw = [np.array(t, dtype=int) for t in TY.tw]
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
        talive = np.array([walive[t].any() for t in tw])
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
            wn[tw[i]] = False
        # circulation support
        idx = [j for j in range(len(W)) if wn[j]]
        if idx:
            inscc = scc_edges([(W[j][:-1], W[j][1:]) for j in idx])
            for k, j in enumerate(idx):
                if k not in inscc:
                    wn[j] = False
        changed = (wn != walive).any() or (Sn != S).any()
        log("ac it", it, "windows", int(wn.sum()), "types", int(sum(wn[t].any() for t in tw)), "slots", int(Sn.sum()),
            flush=True)
        S, walive = Sn, wn
        if not changed or not walive.any():
            break
    return walive, S


def main():
    phi0 = json.loads(sys.argv[1]); m, rm, rp = int(sys.argv[2]), sys.argv[3], sys.argv[4]
    mask = sys.argv[5] if len(sys.argv) > 5 else None
    phi, g, TY, maxval = VM.setup(phi0, m, rm, rp)
    wmask = [set(v) <= set(mask) for v in TY.windows] if mask else None
    print("phi0", phi0, "m", m, "rm", rm, "rp", rp, "mask", mask, "windows", len(TY.windows), "types", TY.N, flush=True)
    walive, S = propagate(TY, g, maxval, wmask=wmask)
    print("surviving windows", int(walive.sum()), ["".join(v) for j, v in enumerate(TY.windows) if walive[j]][:40])
    print("RESULT", "empty" if not walive.any() else "survives", int(walive.sum()), flush=True)


if __name__ == "__main__":
    main()
