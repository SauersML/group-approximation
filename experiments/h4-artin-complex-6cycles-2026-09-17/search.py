"""Exhaustive bounded search of special 6-cycles x1 y1 x2 y2 x3 y3 in the Artin complex of a
linear spherical Coxeter diagram s_1 - ... - s_n (types ŝ1 < ... < ŝn), with x_i of bottom type
ŝ1 (cosets of A_X, X = S - s_1) and y_i of top type ŝn (cosets of A_Y, Y = S - s_n), and of
quasi-centers z = u A_Y (u in A_X) adjacent to x1, x2, x3.

Parametrisation (Huang, arXiv:2405.12068, def:ncycle): x1 = A_X, y1 = A_Y, x2 = aA_X, y2 = abA_Y,
x3 = abcA_X, y3 = abcdA_Y with a, c in A_Y and b, d in A_X, and y3 ~ x1 iff abcd in A_X A_Y.
The words a..d range over products of <= L signed simple elements of the parabolic, modulo
A_Z (Z = X cap Y) on the right.  All group computations are exact Garside normal forms.
"""
import sys, time, itertools
from garside import Coxeter, Artin

DIAGRAMS = {
    "A2": (2, {(0, 1): 3}),
    "A3": (3, {(0, 1): 3, (1, 2): 3}),
    "B3": (3, {(0, 1): 3, (1, 2): 4}),      # 4-edge on top: s1-s2-s3=4
    "B3r": (3, {(0, 1): 4, (1, 2): 3}),
    "H3": (3, {(0, 1): 3, (1, 2): 5}),      # ordered toward the 5-edge
    "H3r": (3, {(0, 1): 5, (1, 2): 3}),
    "A4": (4, {(0, 1): 3, (1, 2): 3, (2, 3): 3}),
    "B4": (4, {(0, 1): 3, (1, 2): 3, (2, 3): 4}),
    "D4": (4, {(0, 1): 3, (1, 2): 3, (1, 3): 3}),
    "H4": (4, {(0, 1): 3, (1, 2): 3, (2, 3): 5}),
    "H4r": (4, {(0, 1): 5, (1, 2): 3, (2, 3): 3}),
}


class Setup:
    def __init__(self, name, K=3):
        n, md = DIAGRAMS[name]
        self.name = name
        self.W = W = Coxeter(n, md)
        self.A = Artin(W)
        full = (1 << n) - 1
        self.X = full & ~1
        self.Y = full & ~(1 << (n - 1))
        self.Z = self.X & self.Y
        self.K = K
        WX = [w for w in range(W.N) if W.supp[w] & ~self.X == 0]
        WY = [w for w in range(W.N) if W.supp[w] & ~self.Y == 0]
        self.WYX = set(W.mul(y, x) for y in WY for x in WX)
        self.WXY = set(W.inv[w] for w in self.WYX)
        self.WX, self.WY = WX, WY

    def reps(self, mask, L):
        """coset reps of A_mask / A_Z: products of <= L signed simples of W_mask"""
        W, A = self.W, self.A
        Wm = [w for w in range(W.N) if W.supp[w] & ~mask == 0 and w != 0]
        signed = [(A.simple(w), w) for w in Wm] + [(A.inv(A.simple(w)), W.inv[w]) for w in Wm]
        out = {A.coset_key(A.one, self.Z): (A.one, 0)}
        seen = {A.one}
        layer = [(A.one, 0)]
        for _ in range(L):
            new = []
            for g, pw in layer:
                for h, ph in signed:
                    gh = A.mul(g, h)
                    if gh in seen:
                        continue
                    seen.add(gh)
                    new.append((gh, W.mul(pw, ph)))
                    key = A.coset_key(gh, self.Z, Nb=4 * L + 4)
                    if key not in out:
                        out[key] = (gh, W.mul(pw, ph))
            layer = new
        return list(out.values())

    def adj_YX(self, g, K=None):
        """exact for padding K: g in A_Y A_X  (i.e. A_Y ~ gA_X)"""
        return self.A.in_product(g, self.Y, self.X, self.K if K is None else K)

    def adj_XY(self, g, K=None):
        return self.A.in_product(g, self.X, self.Y, self.K if K is None else K)

    def inZ(self, key):
        return key == self.A.coset_key(self.A.one, self.Z)


def run(name, L=1, Lu=1, K=3, limit=None, verbose=True):
    S = Setup(name, K)
    W, A = S.W, S.A
    t0 = time.time()
    RY = [r for r in S.reps(S.Y, L) if r[0] != A.one]
    RX = [r for r in S.reps(S.X, L) if r[0] != A.one]
    RU = S.reps(S.X, Lu)
    print(f"[{name}] |W|={W.N} L={L} Lu={Lu} K={K} |RY|={len(RY)} |RX|={len(RX)} |RU|={len(RU)}", flush=True)
    WXset = set(S.WX)
    stats = dict(cycles=0, trivial=0, found=0, none=0)
    bad = []
    for (a, pa) in RY:
        for (b, pb) in RX:
            ab = A.mul(a, b)
            pab = W.mul(pa, pb)
            for (c, pc) in RY:
                abc = A.mul(ab, c)
                pabc = W.mul(pab, pc)
                if pabc in WXset and A.in_parabolic(abc, S.X, K):
                    continue                      # x3 = x1
                for (d, pd) in RX:
                    pabcd = W.mul(pabc, pd)
                    if pabcd not in S.WXY:
                        continue
                    abcd = A.mul(abc, d)
                    if not S.adj_XY(abcd):
                        continue                  # y3 not adjacent to x1
                    if pabcd in set(S.WY) and A.in_parabolic(abcd, S.Y, K):
                        continue                  # y3 = y1
                    stats["cycles"] += 1
                    # trivial quasi-centres: y1, y2, y3
                    if S.adj_YX(abc) or S.adj_XY(ab) or S.adj_XY(A.mul(A.mul(b, c), d)):
                        stats["trivial"] += 1
                        continue
                    z = None
                    for (u, pu) in RU:
                        pui = W.inv[pu]
                        if W.mul(pui, pa) not in S.WYX or W.mul(pui, pabc) not in S.WYX:
                            continue
                        ui = A.inv(u)
                        if S.adj_YX(A.mul(ui, a)) and S.adj_YX(A.mul(ui, abc)):
                            z = u
                            break
                    if z is None:
                        stats["none"] += 1
                        bad.append((a, b, c, d))
                        if verbose and len(bad) <= 5:
                            print("  no quasi-centre found:", a, b, c, d, flush=True)
                    else:
                        stats["found"] += 1
                    if limit and stats["cycles"] >= limit:
                        print(stats); return S, bad
    print(f"[{name}] {stats} time={time.time()-t0:.1f}s", flush=True)
    return S, bad


if __name__ == "__main__":
    name = sys.argv[1]
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    Lu = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    K = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    run(name, L, Lu, K)
