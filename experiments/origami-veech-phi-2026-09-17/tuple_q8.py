"""Rank-bounded permutation tuples of Z^2 x| SL_2(Z) with quadratic phi(L).

X_m = scaled Eierlegende Wollmilchsau (8 m^2 small squares). Affine lifts S, T act exactly on
non-corner vertices, but Aff(O) -> SL_2(Z) does not split (every lift of S has s^4 = -1 in Aut = Q8).
Fix: Y = non-corner vertices at scale m0, on which Aff acts exactly and Q8 acts freely; the tuple
acts on X'' = (X_m x Y)/Q8 (diagonal), where Q8 acts trivially, so SL_2(Z) relators hold
up to the bounded corner patch."""
import sys, time
from perm import *
from wms import B as B8, C as C8
from scaled import scale
from affine import affine_map, S_MAT, T_MAT

def params(A, m):
    return [(j, cr) for j in range(8) for cr in ((0,0),(1,0),(0,1),(1,1)) if affine_map(B8, C8, m, A, j, cr) is not None]

auts = list(isos((B8, C8), (B8, C8)))

def aut_on(m, tau):
    n = 8
    return tuple((tau[i]*m + u)*m + v for i in range(n) for u in range(m) for v in range(m))

def build(m, m0, sp, tp):
    b, c = scale(B8, C8, m)
    fS, fT = affine_map(B8, C8, m, S_MAT, *sp), affine_map(B8, C8, m, T_MAT, *tp)
    gS, gT = affine_map(B8, C8, m0, S_MAT, *sp), affine_map(B8, C8, m0, T_MAT, *tp)
    Y = [((i*m0+u)*m0+v) for i in range(8) for u in range(m0) for v in range(m0) if (u, v) != (0, 0)]
    tauX = [aut_on(m, t) for t in auts]; tauXi = [inv(t) for t in tauX]
    tauY = [aut_on(m0, t) for t in auts]
    reps, where = [], {}
    for y in Y:
        if y in where: continue
        o = len(reps); reps.append(y)
        for k, t in enumerate(tauY): where[t[y]] = (o, k)
    assert len(where) == len(Y) and all(len({tY[y] for tY in tauY}) == 8 for y in reps)
    N, d = len(reps), len(b)
    def lift(FX, FY):
        out = [0] * (N * d)
        for o in range(N):
            o2, k = where[FY[reps[o]]]
            ti = tauXi[k]
            for p in range(d):
                out[o*d + p] = o2*d + ti[FX[p]]
        return tuple(out)
    B2 = tuple(o*d + b[p] for o in range(N) for p in range(d))
    C2 = tuple(o*d + c[p] for o in range(N) for p in range(d))
    return B2, C2, lift(fS, gS), lift(fT, gT), N

if __name__ == "__main__":
    m0 = 2
    ms = [int(a) for a in sys.argv[1:]]
    Sp, Tp = params(S_MAT, ms[0]), params(T_MAT, ms[0])
    best = None
    for sp in Sp:
        for tp in Tp:
            B2, C2, S2, T2, N = build(ms[0], m0, sp, tp)
            tot = {k: perm_rank_defect(v) for k, v in relators(B2, C2, S2, T2).items()}
            if best is None or max(tot.values()) < best[0]: best = (max(tot.values()), sp, tp)
    print("chosen lifts", best)
    for m in ms:
        t0 = time.time()
        B2, C2, S2, T2, N = build(m, m0, best[1], best[2])
        tot = {k: perm_rank_defect(v) for k, v in relators(B2, C2, S2, T2).items()}
        Ls = sorted({1, 2, max(1, m//4), max(1, m//2), m})
        phi = {L: perm_rank_defect(comm(power(B2, L), power(C2, L))) for L in Ls}
        print("m=%d N=%d d=%d relator ranks %s max=%d | phi(L) %s | phi(L)/L^2 %s (%.1fs)" % (
            m, N, len(B2), tot, max(tot.values()), phi, {L: round(phi[L]/L**2, 2) for L in Ls}, time.time()-t0))
        sys.stdout.flush()
