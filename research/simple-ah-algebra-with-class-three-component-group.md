---
rg: 2
id: simple-ah-algebra-with-class-three-component-group
kind: claim
title: A simple unital nuclear AH algebra has three unitaries whose triple commutator is an order-two class outside U0
distinct_from:
  stw59-nonabelian-unitary-component-groups: That realizes component groups of class exactly two as central extensions of K1 over equal-dimension towers; this has a nonzero triple commutator, over a Toms trapping tower whose base dimension is about four times the rank.
  u2-triple-samelson-class-three-stage: That is the nonsimple finite stage C(T^2 x S^3, M_2); this carries the same eta-squared commutator into a simple limit.
  toms-trapped-spin-bordism-class: That is the detector over S^4 x X; this applies it with the seed factor T^2 x S^3 to get a class-three witness.
  simple-cstar-unitary-components-class-three: That root asks only for existence; this names the explicit Toms-type tower and adds order two, zero K1 class, and triviality in M_2.
artifacts:
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
  - research/artifacts/class-three-spin-bordism-trapping-part2-2026-09-12.md
---

There are a simple, separable, unital, nuclear, stably finite,
infinite-dimensional AH algebra A and unitaries u_1, u_2, v in A such that

    w = [u_2, [u_1, v]]   is not in U_0(A),

where [x, y] = x y x* y*. So U(A)/U_0(A) has gamma_3 != 1, and it is not
nilpotent of class at most two. The class of w has order exactly two. Its
K_1 class is zero, and diag(w, 1) lies in U_0(M_2(A)).

Construction: Toms's Grassmannian trapping tower (arXiv:2609.09535v1,
Sections 5--6), with the seed factor S^4 replaced by T^2 x S^3. The stages are
A_i = Gamma(End(C^2 (+) Q_i)) over T^2 x S^3 x X_i. The witnesses are
u_1 = alpha(s_1) (+) 1, u_2 = alpha(s_2) (+) 1 and v = omega(z) (+) 1, where
alpha(s) = diag(s, 1) and omega is the inclusion SU(2) ⊂ U(2).

Detection: the trapped spin-bordism class of the triple commutator is
<c_r(Q_i)^2, [X_i]> = 1 times the eta-squared class in Omega^Spin_2 = Z/2 at
every stage.

Credit: the detector, the recursion and the limit lemmas are Toms's. The
eta-squared triple Samelson product is from the lix-sweep lane. The new
steps are the seed replacement and the spin-bordism detection of eta
squared. Complete argument, not independently reviewed. It depends on an
unrefereed preprint.

We do not claim that U(A)/U_0(A) is nilpotent, and we do not compute K_1(A),
the trace simplex or the stable rank.
