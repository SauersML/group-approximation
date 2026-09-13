---
rg: 2
id: simple-ah-algebra-with-class-four-component-group
kind: claim
title: A simple unital nuclear AH algebra has four unitaries whose fourfold commutator is an order-two class outside U0
distinct_from:
  simple-ah-algebra-with-class-three-component-group: That traps eta squared in spin bordism over complex Grassmannians; this traps eta cubed in BSpin_8-bordism over quaternionic Grassmannians Gr_8(H^{8+2d}), where spin bordism is blind.
  u2-quadruple-samelson-class-four-stage: That is the nonsimple stage C(T^3 x S^3, M_2) of class exactly four; this carries its commutator into a simple limit.
  simple-cstar-unitary-components-class-four: That root asks only for existence; this names the tower and adds order two, zero K1 class and triviality in M_2.
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-2026-09-13.md
  - research/artifacts/class-four-lambda-mod-eight-trapping-part2-2026-09-13.md
---

There are a simple, separable, unital, nuclear, stably finite,
infinite-dimensional AH algebra A and unitaries u_1, u_2, u_3, v in A with

    c = [u_3, [u_2, [u_1, v]]]   not in U_0(A).

So gamma_4(U(A)/U_0(A)) != 1. The class of c has order exactly two, its
K_1 class is zero, and diag(c, 1) lies in U_0(M_2(A)).

Construction: Toms's trapping tower (arXiv:2609.09535v1) with seed factor
T^3 x S^3, base X_1 = point, and steps
X_{i+1} = X_i x Gr_8(H^{8+2d_i}), Q_{i+1} = Q_i (+) d_i·zeta_i. The witnesses are
alpha(s_j) (+) 1 and omega(z) (+) 1. Detection: the trapped BSpin_8-bordism
class of c is ±eta^3 at every stage.

Credit: detector, recursion and limit lemmas are Toms's. The eta-cubed
Samelson product and the spin-case seed-factor generalization are from lane
ex-unitary-class-three. New here are the structure on the difference
TX − W_R taken mod 8, and the quaternionic Grassmannian steps. Complete
argument, not independently reviewed. It depends on an unrefereed preprint
and on the unreviewed class-three artifacts.

We do not claim that U(A)/U_0(A) is nilpotent.
