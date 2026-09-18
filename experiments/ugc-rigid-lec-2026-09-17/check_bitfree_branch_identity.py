#!/usr/bin/env python3
"""Exhaustive toy check of the two generic steps of Theorem S* in
research/near-perfect-selectors-die-on-every-rigid-doubled-lec.md.

Setting (doubled LEC).  A 2-to-1 game G: left vertices P with alphabet
Sigma_P = F_2^r (size 2^r), right vertices Q with alphabet Sigma_Q of size
2^(r-1).  Constraint e = (p, q) carries a 2-to-1 onto map pi_e and an
evaluation ev_e : Sigma_P -> F_2 (the value of the left label at the
direction x_e).  An orientation o_e : Sigma_P -> {0,1} is injective on every
fibre of pi_e.  The doubled lift U_o has right alphabet Sigma_Q x {0,1} and
the bijective constraint sigma -> (pi_e(sigma), o_e(sigma)).  Its bit
function is G_e(tau, b) := ev_e(the unique sigma sent to (tau, b)).

Checked, over random instances and all labellings of small instances:

 (1) forgetful step: every lift labelling W satisfies
     val_G(forget(W)) >= val_(U_o)(W), and val(U_o) <= val(G);
 (2) bit-free branch identity: for every plain labelling H0, every bit
     assignment b and every orientation o, if (H0, b) satisfies the oriented
     constraint e, then G_e(H0_q, b_q) = ev_e(H0_p);
 (3) witness step: if W has lift value >= 1 - xi and forget(W) agrees with
     H0 at both endpoints outside mass zeta, then (H0, bits of W) agrees with
     W at both endpoints outside the same mass zeta.

Exit code 0 iff all checks pass.
"""
import itertools
import random

random.seed(20260918)


def rand_instance(nP, nQ, r, nE):
    SP = list(range(2 ** r))
    SQ = list(range(2 ** (r - 1)))
    edges = []
    for _ in range(nE):
        p, q = random.randrange(nP), random.randrange(nQ)
        perm = SP[:]
        random.shuffle(perm)
        pi = {}
        for i, s in enumerate(perm):
            pi[s] = SQ[i // 2]          # 2-to-1 onto
        ev = {s: random.randrange(2) for s in SP}
        w = random.random() + 0.1
        edges.append((p, q, pi, ev, w))
    tot = sum(e[4] for e in edges)
    edges = [(p, q, pi, ev, w / tot) for (p, q, pi, ev, w) in edges]
    return SP, SQ, edges


def rand_orientation(SP, edges):
    ors = []
    for (p, q, pi, ev, w) in edges:
        fib = {}
        for s in SP:
            fib.setdefault(pi[s], []).append(s)
        o = {}
        for t, pair in fib.items():
            assert len(pair) == 2
            bit = random.randrange(2)
            o[pair[0]], o[pair[1]] = bit, 1 - bit
        ors.append(o)
    return ors


def val_plain(edges, A, B):
    return sum(w for (p, q, pi, ev, w) in edges if pi[A[p]] == B[q])


def val_lift(edges, ors, A, B, bits):
    return sum(w for (p, q, pi, ev, w), o in zip(edges, ors)
               if pi[A[p]] == B[q] and o[A[p]] == bits[q])


def bitfn(pi, o, ev, SP, t, b):
    pre = [s for s in SP if pi[s] == t and o[s] == b]
    assert len(pre) == 1          # the lifted constraint is a bijection
    return ev[pre[0]]


def main():
    trials = 0
    # exhaustive over labellings on small instances
    for inst in range(40):
        nP, nQ, r = 2, 2, 2
        SP, SQ, edges = rand_instance(nP, nQ, r, nE=5)
        ors = rand_orientation(SP, edges)
        best_plain = 0.0
        best_lift = 0.0
        for A in itertools.product(SP, repeat=nP):
            for B in itertools.product(SQ, repeat=nQ):
                vp = val_plain(edges, A, B)
                best_plain = max(best_plain, vp)
                for bits in itertools.product((0, 1), repeat=nQ):
                    vl = val_lift(edges, ors, A, B, bits)
                    best_lift = max(best_lift, vl)
                    assert vp >= vl - 1e-12                       # (1)
                    for (p, q, pi, ev, w), o in zip(edges, ors):   # (2)
                        if pi[A[p]] == B[q] and o[A[p]] == bits[q]:
                            assert bitfn(pi, o, ev, SP, B[q], bits[q]) == ev[A[p]]
                    trials += 1
        assert best_lift <= best_plain + 1e-12
    # (3) witness step on random larger instances
    for inst in range(200):
        nP, nQ, r = 6, 6, 3
        SP, SQ, edges = rand_instance(nP, nQ, r, nE=30)
        ors = rand_orientation(SP, edges)
        A = [random.choice(SP) for _ in range(nP)]
        B = [random.choice(SQ) for _ in range(nQ)]
        bits = [random.randrange(2) for _ in range(nQ)]
        # H0: perturb some endpoints
        A0 = [a if random.random() < 0.7 else random.choice(SP) for a in A]
        B0 = [t if random.random() < 0.7 else random.choice(SQ) for t in B]
        zeta = sum(w for (p, q, pi, ev, w) in edges
                   if A0[p] != A[p] or B0[q] != B[q])
        zeta2 = sum(w for (p, q, pi, ev, w) in edges
                    if A0[p] != A[p] or (B0[q], bits[q]) != (B[q], bits[q]))
        assert abs(zeta - zeta2) < 1e-12                           # (3)
        trials += 1
    print(f"all checks pass ({trials} labelling/bit configurations)")


if __name__ == "__main__":
    main()
