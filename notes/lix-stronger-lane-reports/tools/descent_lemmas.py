#!/usr/bin/env python3
"""sp-descent model test 2: every identity the Lean proof will state, checked numerically.

The Lean route, in one paragraph.  Write W_a for "wedge with xi_a" (insert `g` in slot `a`
with the Koszul prefix sign) and P_a for its adjoint d/d xi_a.  Then D = sum_a W_a,
H = P_0, T is the cyclic slot shift with sp-design's sign, N = sum_k T^k.  Put
R := sum_{a in Z/p} W_a W_{a+1}  (the CYCLIC "domino" operator).  The claims:

  (A)  W_a W_a = 0,  W_a W_b = - W_b W_a
  (B)  P_a W_b + W_b P_a = [a = b]
  (C)  T W_a = W_{a-1} T,   T^p = 1
  (E)  D D = 0,  D H + H D = 1
  (F)  R commutes with every W_b, with T and with N
  (G)  N(e_{{0,1}}) = R(e_{}),  i.e. sum_j T^j (xi_0 ^ xi_1) = sum_a xi_a ^ xi_{a+1}
  (H)  <P_a u, v> = <u, W_a v>,  <T u, v> = <u, T^{-1} v>,  <N u, v> = <u, N v>
  (I)  the dual sequence  X_0 = xi_0,  X_{k+1} = W_0 N W_0 (T^{-1} - 1) X_k
       satisfies  X_k = W_0 R^k (1)
  (J)  <B_m, X_0> = <B_0, X_m>  with  B_0 = omega,  B_{k+1} = (T-1) H N H B_k
  (K)  P_i R = R P_i + W_{i+1} - W_{i-1}
  (L)  [e_{i..i+2k-1}] R^k (1) = k!   for  1 <= i,  i + 2k <= p
"""
import sys
from itertools import combinations
from descent_ext import (wedge_gen, partial, addto, op_sub, op_T, op_N, op_s,
                         op_D, op_H, op_wedge0, red, primal_descent, dual_descent)


def basis(p):
    return [tuple(c) for k in range(p + 1) for c in combinations(range(p), k)]


def W(p, a, v):
    out = {}
    for S, c in v.items():
        r = wedge_gen(a, S)
        if r:
            addto(out, r[1], r[0] * c)
    return out


def P(p, a, v):
    out = {}
    for S, c in v.items():
        r = partial(a, S)
        if r:
            addto(out, r[1], r[0] * c)
    return out


def R(p, v):
    out = {}
    for a in range(p):
        for S, c in W(p, a, W(p, (a + 1) % p, v)).items():
            addto(out, S, c)
    return out


def Rk(p, v, k):
    for _ in range(k):
        v = R(p, v)
    return v


def pair(u, v):
    return sum(c * v.get(S, 0) for S, c in u.items())


def one(p):
    return {(): 1}


def omega(p):
    return {tuple(range(p)): 1}


def eq(a, b):
    return op_sub(a, b) == {}


def interval_word(p, i, ln):
    return tuple(range(i, i + ln))


def factorial(n):
    r = 1
    for t in range(2, n + 1):
        r *= t
    return r


if __name__ == "__main__":
    primes = [int(a) for a in sys.argv[1:]] or [3, 5, 7]
    for p in primes:
        B = basis(p)
        rep = []

        def chk(name, ok):
            rep.append(f"{name}={'OK' if ok else 'FAIL'}")

        # (A)
        chk("A.WW0", all(W(p, a, W(p, a, {S: 1})) == {} for a in range(p) for S in B))
        chk("A.anti", all(eq(W(p, a, W(p, b, {S: 1})),
                            {k: -c for k, c in W(p, b, W(p, a, {S: 1})).items()})
                          for a in range(p) for b in range(p) for S in B))
        # (B)
        okB = True
        for a in range(p):
            for b in range(p):
                for S in B:
                    v = {S: 1}
                    lhs = P(p, a, W(p, b, v))
                    for k, c in W(p, b, P(p, a, v)).items():
                        addto(lhs, k, c)
                    rhs = v if a == b else {}
                    okB &= eq(lhs, rhs)
        chk("B.CAR", okB)
        # (C)
        chk("C.TW", all(eq(op_T(p, W(p, a, {S: 1})), W(p, (a - 1) % p, op_T(p, {S: 1})))
                        for a in range(p) for S in B))
        okT = True
        for S in B:
            v = {S: 1}
            for _ in range(p):
                v = op_T(p, v)
            okT &= eq(v, {S: 1})
        chk("C.Tp", okT)
        # (E)
        okE = True
        for S in B:
            v = {S: 1}
            okE &= op_D(p, op_D(p, v)) == {}
            lhs = op_D(p, op_H(p, v))
            for k, c in op_H(p, op_D(p, v)).items():
                addto(lhs, k, c)
            okE &= eq(lhs, v)
        chk("E.DD.DH", okE)
        # (F)
        chk("F.RW", all(eq(R(p, W(p, b, {S: 1})), W(p, b, R(p, {S: 1})))
                        for b in range(p) for S in B))
        chk("F.RT", all(eq(R(p, op_T(p, {S: 1})), op_T(p, R(p, {S: 1}))) for S in B))
        chk("F.RN", all(eq(R(p, op_N(p, {S: 1})), op_N(p, R(p, {S: 1}))) for S in B))
        # (G)
        chk("G.NR", eq(op_N(p, {(0, 1): 1}), R(p, one(p))))
        # (H)
        okH = True
        for a in range(p):
            for S in B:
                for S2 in B:
                    u, v = {S: 1}, {S2: 1}
                    okH &= pair(P(p, a, u), v) == pair(u, W(p, a, v))
        chk("H.adjPW", okH)
        chk("H.adjT", all(pair(op_T(p, {S: 1}), {S2: 1})
                          == pair({S: 1}, op_T(p, {S2: 1}, inv=True))
                          for S in B for S2 in B))
        chk("H.adjN", all(pair(op_N(p, {S: 1}), {S2: 1}) == pair({S: 1}, op_N(p, {S2: 1}))
                          for S in B for S2 in B))
        # (I)
        _, xs = dual_descent(p, mod=None)
        chk("I.dual", all(eq(xs[k], W(p, 0, Rk(p, one(p), k))) for k in range(len(xs))))
        # (J) pairing invariance across the descent
        m = (p - 1) // 2
        Bs = [omega(p)]
        for _ in range(m):
            Bs.append(red(op_s(p, op_H(p, op_N(p, op_H(p, Bs[-1])))), p))
        chk("J.pair", all(pair(Bs[m - t], xs[t]) % p == pair(Bs[0], xs[m]) % p
                          for t in range(m + 1)))
        chk("J.val", pair(Bs[m], xs[0]) % p == factorial(m) % p)
        # (K)
        okK = True
        for i in range(p):
            for S in B:
                v = {S: 1}
                lhs = P(p, i, R(p, v))
                rhs = R(p, P(p, i, v))
                for k, c in W(p, (i + 1) % p, v).items():
                    addto(rhs, k, c)
                for k, c in W(p, (i - 1) % p, v).items():
                    addto(rhs, k, -c)
                okK &= eq(lhs, rhs)
        chk("K.PR", okK)
        # (L)
        okL = True
        for k in range(0, m + 1):
            for i in range(1, p):
                if i + 2 * k <= p:
                    okL &= Rk(p, one(p), k).get(interval_word(p, i, 2 * k), 0) == factorial(k)
        chk("L.interval", okL)
        print(f"p={p:3d}: " + "  ".join(rep))

    print()
    print("### the two cyclic-shift conventions (sp-design's T vs its inverse)")
    for p in primes + ([11] if 11 not in primes else []):
        m = (p - 1) // 2
        for inv in (False, True):
            A = omega(p)
            Widx = p - 1
            while Widx > 0:
                Y = op_H(p, A)
                A = red(op_N(p, Y) if Widx % 2 == 0 else op_s(p, Y, inv=inv), p)
                Widx -= 1
            print(f"  p={p:3d} op = (T{'^-1' if inv else ''} - 1): c_1 = {A.get((0,), 0)}"
                  f"   m! mod p = {factorial(m) % p}")

    print()
    print("### the evaluation sign: only the word (g,f,...,f) survives the AW pairing")
    for p in primes:
        # p-fold AW diagonal of the 1-simplex, cut sequences over {0,1}
        from itertools import product as iproduct
        surv = []
        for cuts in iproduct(range(2), repeat=p - 1):
            if any(cuts[t] > cuts[t + 1] for t in range(len(cuts) - 1)):
                continue
            idx = (0,) + cuts + (1,)
            faces = tuple(tuple(range(idx[t], idx[t + 1] + 1)) for t in range(p))
            if all(fc != (0,) for fc in faces):
                surv.append(faces)
        print(f"  p={p:3d}: AW terms with no vertex-0 factor: {surv}")
