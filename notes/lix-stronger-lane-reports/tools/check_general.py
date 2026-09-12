#!/usr/bin/env python3
"""sp-descent model test 3: the two general-y identities the Lean proof states."""
import sys
from itertools import combinations
from descent_ext import op_T, op_N, op_sub, red
from descent_lemmas import W, P, R, basis, eq, one

def Tpow(p, v, k):
    for _ in range(k):
        v = op_T(p, v)
    return v

if __name__ == "__main__":
    for p in [3, 5, 7]:
        B = basis(p)
        # T-invariant elements: N(z) for every basis z, plus R^k(1)
        invs = [op_N(p, {S: 1}) for S in B]
        invs += [{(): 1}]
        cur = {(): 1}
        for _ in range((p - 1) // 2):
            cur = R(p, cur)
            invs.append(dict(cur))
        bad1 = bad2 = 0
        for y in invs:
            if op_sub(op_T(p, y), y):
                bad1 += 1
                continue
            lhs = op_N(p, W(p, 0, W(p, 1, y)))
            rhs = R(p, y)
            if not eq(lhs, rhs):
                bad2 += 1
        # T^k W_a = W_{a-k} T^k
        bad3 = 0
        for k in range(p):
            for a in range(p):
                for S in B:
                    v = {S: 1}
                    l = Tpow(p, W(p, a, v), k)
                    r = W(p, (a - k) % p, Tpow(p, v, k))
                    if not eq(l, r):
                        bad3 += 1
        print(f"p={p}: T-invariance failures {bad1}; "
              f"N(xi0^xi1^y) = rho^y failures {bad2} over {len(invs)} invariant y; "
              f"T^k W_a = W_(a-k) T^k failures {bad3}")
