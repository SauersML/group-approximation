#!/usr/bin/env python3
"""Exact thickenability of the standard Akbulut-Kirby words.

AK(n) = < x, y | x^n y^-(n+1), x y x y^-1 x^-1 y^-1 >  (equivalently
x^n = y^(n+1), xyx = yxy; up to the swap x<->y this is Lackenby's
<x,y | xyx=yxy, x^(k+1)=y^k>).  Search space: all prod_g (d_g - 1)! cyclic
orders (orient) and additionally per-generator same/reverse (either).  Method:
thicken.dfs (complete branch and bound); for n <= 3 also thicken.brute (full
enumeration, no pruning).
"""
import time
import thicken as T


def ak(n):
    return ["x" * n + "Y" * (n + 1), "xyxYXY"]


def main():
    for n in range(1, 6):
        rels = ak(n)
        K = T.Complex(rels)
        row = [f"AK({n})", rels, f"E={K.E} V={K.V} c={K.c} F_target={K.F_target}",
               f"d_x={K.occ['x']} d_y={K.occ['y']}"]
        for v in ("orient", "either"):
            t = time.time()
            ok, wit, nodes = T.dfs(K, v)
            row.append(f"{v}: {ok} (dfs nodes {nodes}, {time.time()-t:.2f}s)")
            if ok:
                row.append(f"witness {wit}")
            if n <= 3:
                okb, witb, cnt = T.brute(K, v)
                row.append(f"brute {v}: {okb} after {cnt} rotations")
        print(" | ".join(str(r) for r in row), flush=True)


if __name__ == "__main__":
    main()
