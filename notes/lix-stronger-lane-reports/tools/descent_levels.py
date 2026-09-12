#!/usr/bin/env python3
"""lix-descent model test: the degree-one descent at EVERY level, p = 3, 5, 7, 11, 13.

Uses sp-descent's exterior re-description (descent_ext.py, checked there against sp-design's word
model on every basis element at p = 3, 5, 7).  Conventions are the Lean files' (OddPDescent*.lean):
    eD = xi-sum ^ (-),  eH = d/d xi_0,  eT = algebra map xi_j |-> xi_{j-1}  (sp-design's T),
    eN = sum_{k<p} eT^k,  eRound = (eT - 1) o eH o eN o eH,  eA k = eRound^k (omega),
    eY1 k = eH (eA k), eMid k = eN (eY1 k), eY2 k = eH (eMid k), eA (k+1) = (eT - 1) (eY2 k),
    eX k = xi_0 ^ rho^k,  rho = sum_a xi_a ^ xi_{a+1},  eRoundStar = (xi_0^) o eN o (xi_0^) o (eT^{p-1} - 1).
Reports, per prime:
  (a) the sign vector of N on v_0 = f (x) g^{(p-1)} (bidegree (0,1,...,1)), read by the position j of f;
  (b) at every level k = 0..m: support sizes of eA/eY1/eMid/eY2 over Z, whether eD eA = 0 and the two
      primitive identities hold over Z and mod p;
  (c) the dual sequence: eX (k+1) == eRoundStar (eX k) over Z at every k, and eX k == k! * (domino sum);
  (d) the pairing identity <eA j, eX k> ... in the form <eA m, xi_0> = <omega, eX m>, and the value m!;
  (e) the interval coefficient [e_{1..2k}] rho^k = k! for every k <= m (the Lean lemma eR_pow_interval);
  (f) the direction trap: the value with eT replaced by eT^{-1}.
"""
import sys
from math import factorial
sys.path.insert(0, ".")
from descent_ext import (op_D, op_H, op_T, op_N, op_s, op_sub, op_wedge0, wedge_gen, red, addto,
                         domino_element, scal, primal_descent)


def op_wedge(j, v):
    out = {}
    for S, c in v.items():
        r = wedge_gen(j, S)
        if r:
            addto(out, r[1], r[0] * c)
    return out


def op_rho(p, v):
    out = {}
    for a in range(p):
        for S, c in op_wedge(a, op_wedge((a + 1) % p, v)).items():
            addto(out, S, c)
    return out


def op_Tpow(p, v, k):
    for _ in range(k):
        v = op_T(p, v)
    return v


def pair(u, v):
    return sum(c * v.get(S, 0) for S, c in u.items())


def run(p):
    m = (p - 1) // 2
    omega = {tuple(range(p)): 1}
    print(f"=== p = {p}, m = {m}")
    # (a) sign vector of N on v_0 = e_{1..p-1}
    v0 = {tuple(range(1, p)): 1}
    Nv0 = op_N(p, v0)
    eps = [Nv0.get(tuple(x for x in range(p) if x != j), 0) for j in range(p)]
    print(f"  (a) N v_0 coefficients by position j of f: {eps};  equals (-1)^j: "
          f"{eps == [(-1) ** j for j in range(p)]};  support {len(Nv0)} (expected p)")
    # (b) primal levels over Z and mod p
    A = dict(omega)
    rows = []
    allz = allp = True
    for k in range(m + 1):
        DA = op_D(p, A)
        Y1 = op_H(p, A)
        Mid = op_N(p, Y1)
        Y2 = op_H(p, Mid)
        cocZ, cocP = red(DA, None) == {}, red(DA, p) == {}
        pr1Z = red(op_sub(op_D(p, Y1), A), None) == {}
        pr1P = red(op_sub(op_D(p, Y1), A), p) == {}
        DMid = op_D(p, Mid)
        pr2Z = red(op_sub(op_D(p, Y2), Mid), None) == {}
        pr2P = red(op_sub(op_D(p, Y2), Mid), p) == {}
        allp = allp and cocP and pr1P and (k == m or (red(DMid, p) == {} and pr2P))
        allz = allz and cocZ and pr1Z
        rows.append((k, len(A), len(Y1), len(Mid), len(Y2), cocZ, cocP, pr1Z, pr1P, pr2Z, pr2P))
        if k < m:
            A = op_s(p, Y2)
    for r in rows:
        print(f"  (b) level {r[0]}: |A|={r[1]} |Y1|={r[2]} |Mid|={r[3]} |Y2|={r[4]} | "
              f"D A=0 over Z {r[5]}, mod p {r[6]} | D Y1=A over Z {r[7]}, mod p {r[8]} | "
              f"D Y2=Mid over Z {r[9]}, mod p {r[10]}")
    print(f"  (b) every cocycle/primitive identity mod p at every level: {allp}")
    value = A.get((0,), 0)
    print(f"  (d) <A_m, xi_0> over Z = {value};  m! = {factorial(m)};  equal {value == factorial(m)};"
          f"  mod p {value % p}")
    # (c) dual sequence
    X = {(0,): 1}
    rhok = {(): 1}
    okc = okdom = True
    for k in range(m + 1):
        Xk = op_wedge(0, rhok)
        if red(op_sub(X, Xk), None) != {}:
            okc = False
        if red(op_sub(Xk, scal(domino_element(p, k), factorial(k))), None) != {}:
            okdom = False
        # (e) interval coefficient
        I = tuple(range(1, 1 + 2 * k))
        if k >= 1 and rhok.get(I, 0) != factorial(k):
            print(f"  (e) FAIL at k={k}: [e_1..2k] rho^k = {rhok.get(I, 0)}")
        if k < m:
            s = op_sub(op_Tpow(p, X, p - 1), X)
            X = op_wedge(0, op_N(p, op_wedge(0, s)))
            rhok = op_rho(p, rhok)
    print(f"  (c) eX_(k+1) = eRoundStar(eX_k) reproduces xi_0^rho^k at every k<=m: {okc};"
          f"  xi_0^rho^k = k!*dominoes: {okdom}")
    print(f"  (e) [e_(1..2k)] rho^k = k! for k = 1..m: checked above (no FAIL line = pass)")
    top = pair(omega, op_wedge(0, rhok))
    print(f"  (d) <omega, eX_m> = {top};  equals <A_m, xi_0>: {top == value}")
    # (f) direction trap
    Ainv = dict(omega)
    for k in range(m):
        Ainv = op_s(p, op_H(p, op_N(p, op_H(p, Ainv))), inv=True)
    vinv = Ainv.get((0,), 0)
    print(f"  (f) with eT^(-1): value over Z {vinv}, mod p {vinv % p};  ((p-1)/2)! mod p {factorial(m) % p}")


if __name__ == "__main__":
    for p in [int(a) for a in sys.argv[1:]] or [3, 5, 7, 11, 13]:
        run(p)
