"""Faster bounded special-6-cycle search with per-slot word lengths (see search.py for the model).

Ball B(La,Lb,Lc,Ld; K): a in R_Y(La), b in R_X(Lb), c in R_Y(Lc), d in R_X(Ld) (products of <= L signed
simple elements modulo A_Z on the right), such that the six vertices are pairwise distinct as tested
at padding K and abcd lies in Delta_X^{-2K} A_X^+ A_Y^+ Delta_Y^{-2K} (so y3 = abcdA_Y ~ x1).
Every cycle in the ball is tested for a quasi-centre u A_Y, u in R_X(Lu) plus y1,y2,y3.
A found quasi-centre is an exact certificate.
"""
import sys, time, json
from search import Setup


def min_rep(W, w, mask):
    while True:
        c = W.rd[w] & mask
        if not c:
            return w
        i = (c & -c).bit_length() - 1
        w = W.rmul[w][i]


def run(name, Ls=(1, 1, 1, 1), Lu=1, K=3, out=None, Lu2=0, K2=0):
    S = Setup(name, K)
    W, A = S.W, S.A
    t0 = time.time()
    RYs = {L: [r for r in S.reps(S.Y, L) if r[0] != A.one] for L in set((Ls[0], Ls[2]))}
    RXs = {L: [r for r in S.reps(S.X, L) if r[0] != A.one] for L in set((Ls[1], Ls[3]))}
    RU = S.reps(S.X, Lu)
    RUs = sorted(RU, key=lambda r: len(r[0][1]) + abs(r[0][0]))
    RUinv = [(A.inv(u), W.inv[pu], u) for (u, pu) in RUs]
    Ra, Rb, Rc, Rd = RYs[Ls[0]], RXs[Ls[1]], RYs[Ls[2]], RXs[Ls[3]]
    print(f"[{name}] Ls={Ls} Lu={Lu} K={K} sizes={len(Ra),len(Rb),len(Rc),len(Rd)} |RU|={len(RU)}", flush=True)
    clsY = [min_rep(W, w, S.Y) for w in range(W.N)]
    byclass = {}
    for (d, pd) in Rd:
        byclass.setdefault(clsY[pd], []).append((d, pd))
    WXreps = sorted(set(min_rep(W, x, S.Z) for x in S.WX))
    WXset = set(S.WX)
    WYset = set(S.WY)
    stats = dict(tuples_abc=0, cycles=0, trivial=0, found=0, none=0)
    ulen = {}
    bad = []
    for (a, pa) in Ra:
        for (b, pb) in Rb:
            ab = A.mul(a, b)
            pab = W.mul(pa, pb)
            for (c, pc) in Rc:
                abc = A.mul(ab, c)
                pabc = W.mul(pab, pc)
                stats["tuples_abc"] += 1
                if pabc in WXset and A.in_parabolic(abc, S.X, K):
                    continue
                ip = W.inv[pabc]
                for xr in WXreps:
                    cl = clsY[W.mul(ip, xr)]
                    for (d, pd) in byclass.get(cl, ()):
                        abcd = A.mul(abc, d)
                        if not S.adj_XY(abcd):
                            continue
                        if W.mul(pabc, pd) in WYset and A.in_parabolic(abcd, S.Y, K):
                            continue
                        stats["cycles"] += 1
                        if S.adj_YX(abc) or S.adj_XY(ab) or S.adj_XY(A.mul(A.mul(b, c), d)):
                            stats["trivial"] += 1
                            continue
                        z = None
                        for idx, (ui, pui, u) in enumerate(RUinv):
                            if W.mul(pui, pa) not in S.WYX or W.mul(pui, pabc) not in S.WYX:
                                continue
                            if S.adj_YX(A.mul(ui, a)) and S.adj_YX(A.mul(ui, abc)):
                                z = u
                                break
                        if z is None:
                            stats["none"] += 1
                            bad.append((a, b, c, d))
                            if len(bad) <= 5:
                                print("  no quasi-centre found:", a, b, c, d, flush=True)
                        else:
                            stats["found"] += 1
                            key = (z[0], len(z[1]))
                            ulen[str(key)] = ulen.get(str(key), 0) + 1
    retry = dict(Lu2=Lu2, K2=K2, resolved=0, unresolved=0)
    unresolved = []
    if bad and Lu2:
        RU2 = sorted(S.reps(S.X, Lu2), key=lambda r: len(r[0][1]) + abs(r[0][0]))
        RU2inv = [(A.inv(u), W.inv[pu], u) for (u, pu) in RU2]
        retry["RU2"] = len(RU2)
        for (a, b, c, d) in bad:
            abc = A.mulmany(a, b, c)
            ok = False
            for (ui, pui, u) in RU2inv:
                if S.adj_YX(A.mul(ui, a), K2) and S.adj_YX(A.mul(ui, abc), K2):
                    ok = True
                    break
            if ok:
                retry["resolved"] += 1
            else:
                retry["unresolved"] += 1
                unresolved.append((a, b, c, d))
    dt = time.time() - t0
    print(f"[{name}] Ls={Ls} {stats} retry={retry} qc(k,len)={ulen} time={dt:.1f}s", flush=True)
    if out:
        with open(out, "a") as f:
            f.write(json.dumps(dict(group=name, Ls=Ls, Lu=Lu, K=K, stats=stats, retry=retry, qc=ulen,
                                    bad=[list(map(list, [x for x in t])) for t in bad[:50]], unresolved=[list(map(list, t)) for t in unresolved[:200]], seconds=round(dt, 1))) + "\n")
    return S, bad


if __name__ == "__main__":
    name = sys.argv[1]
    Ls = tuple(int(x) for x in sys.argv[2].split(","))
    Lu = int(sys.argv[3]); K = int(sys.argv[4])
    out = sys.argv[5] if len(sys.argv) > 5 else None
    Lu2 = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    K2 = int(sys.argv[7]) if len(sys.argv) > 7 else K
    run(name, Ls, Lu, K, out, Lu2, K2)
