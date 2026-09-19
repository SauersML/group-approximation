"""Exact orders of the level quotients G_k of Bbar_e = <b,d> acting on the extended word tree.

Letter-level self-similar structure (from the closed form in mult.py), alphabet Z/m:
    b = (id on the first letter; section at letter x is d^(3^x))
    d = (first letter x -> T x; section at every letter is b)
with T = 3^-1 mod m, composition g*h = g o h (apply h first).
Sections of every element depend on the letter x only through x mod M, M = 2^(e-4)
(3^x mod n depends on x mod 2^(e-4), n = m/4 = ord d), so an element of G_k is
    (s in Z/n, (h_r)_{r in Z/M} with h_r in G_(k-1)),   acting by  x w -> T^s x . h_(x mod M)(w).
Right composition:  g o b = (s, r -> h_r o d^(3^r)),   g o d = (s+1, r -> h_(T r mod M) o b).
We enumerate G_k by closing {1} under right composition with b and d (finite group).
usage: python3 levels.py e kmax [M]    (M defaults to 2^(e-4), at least 2)
"""
import sys, math
e = int(sys.argv[1]); kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
m = 2 ** e; n = m // 4; T = pow(3, -1, m)
M = int(sys.argv[3]) if len(sys.argv) > 3 else max(2 ** (e - 4), 2)
pw = [pow(3, r, n) for r in range(M)]
Tr = [(T * r) % M for r in range(M)]
def build(kmax, verbose=True):
    Rb, Rd = [0], [0]
    sizes = []; prev = None; elems = None
    for k in range(1, kmax + 1):
        # tables for h o d^v for the needed v
        need = sorted(set(pw))
        Rdv = {}
        cur = list(range(len(Rd)))
        v = 0
        for target in need:
            while v < target:
                cur = [Rd[i] for i in cur]; v += 1
            Rdv[target] = cur
        idx = {}; elems = []
        def get(x):
            j = idx.get(x)
            if j is None:
                j = len(elems); idx[x] = j; elems.append(x)
            return j
        one = (0,) + (0,) * M
        get(one)
        nb, nd = [], []
        i = 0
        while i < len(elems):
            s, h = elems[i][0], elems[i][1:]
            gb = (s,) + tuple(Rdv[pw[r]][h[r]] for r in range(M))
            gd = ((s + 1) % n,) + tuple(Rb[h[Tr[r]]] for r in range(M))
            nb.append(get(gb)); nd.append(get(gd))
            i += 1
        Rb, Rd = nb, nd
        N = len(elems)
        sizes.append(N)
        if verbose: print("e=%d M=%d level %d: |G_k| = %d = 2^%.3f" % (e, M, k, N, math.log2(N)), flush=True)
        del idx
    return Rb, Rd, elems, sizes

if __name__ == '__main__':
    build(kmax)
