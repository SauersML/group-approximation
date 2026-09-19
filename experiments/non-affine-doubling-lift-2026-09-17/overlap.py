"""Exact support of c1 on one bulk period at delta-scale n, and the overlaps
supp(c1) cap (supp(c1) + k); then exact w_k on the overlap components.

Bulk: s0 is affine (slope 8) on [4,8), so for x in delta^n([4,8)),
s(x + 2^n) = s(x) + 8*4^n and tau commutes with T_{2^n}: the germ picture is
2^n-periodic there.  We take the period [P, P + 2^n) with P = delta^n(5)."""
import sys
import time
from fast import *


def bulk_period(ch, n):
    P = fx(5)
    for _ in range(n):
        P = ch.delta(P)[0]
    return P, P + (ONE << n)


def periodic_support(e, P, L, pad):
    ivs, npc = support(e['c1'], P - pad, P + L + pad)
    return ivs, npc


def overlaps(ivs, K):
    out = []
    j = 0
    sh = [(a + K, b + K) for a, b in ivs]
    for a, b in ivs:
        for c, d in sh:
            lo, hi = max(a, c), min(b, d)
            if lo < hi:
                out.append((lo, hi))
    return out


if __name__ == "__main__":
    n = int(sys.argv[1])
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    ch = nonaffine()
    e = elements(ch)
    P, Q = bulk_period(ch, n)
    L = Q - P
    t = time.time()
    pad = (kmax + 4) * ONE
    ivs, npc = periodic_support(e, P, L, pad)
    print(f"scale {n}: period [{f(P)}, {f(Q)}) pieces {npc} comps {len(ivs)} ({time.time()-t:.0f}s)")
    inper = [(a, b) for a, b in ivs if P <= a < Q]
    print("  comps per period:", len(inper), " support measure per period:",
          round(f(sum(b - a for a, b in inper)), 4))
    for k in range(1, kmax + 1):
        ov = [(a, b) for a, b in overlaps(ivs, k * ONE) if P <= a < Q]
        if not ov:
            print(f"  k={k:2d}: no overlap")
            continue
        wk_ = wk(ch, k)
        moved = []
        for a, b in ov:
            wiv, _ = support(wk_, a, b)
            moved += wiv
        m = sum(b - a for a, b in moved)
        print(f"  k={k:2d}: overlap comps {len(ov)} measure {f(sum(b-a for a,b in ov)):.4g};"
              f" w_k moves measure {f(m):.4g} in {len(moved)} comps"
              + (f", first at {f(moved[0][0]):.6g}" if moved else ""))
        sys.stdout.flush()
