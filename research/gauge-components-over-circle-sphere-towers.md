---
rg: 2
id: gauge-components-over-circle-sphere-towers
kind: claim
title: Gauge component groups over S^1 x S^(2n-1) x projective spaces are nonabelian central extensions of K^1 by Z/n!
distinct_from:
  stw59-exact-factorial-unitary-component-groups: That computes the whole group Z/n! over the even-cell base S^(2n) x Y, where K^1 vanishes; this base has odd cells, so the group is an extension of the nonzero group K^1(X) and a commutator is nontrivial.
artifacts:
  - research/artifacts/stw59-nonabelian-unitary-component-groups-2026-09-11.md
---

Let n>=2 and Y a finite product of complex projective spaces of total
complex dimension m. Put H = direct-sum_j L_j^(direct-sum d_j),
X = S^1 x S^(2n-1) x Y and E = C^n direct-sum H, so rank E = n+m and
dim X = 2(n+m). For G(E) = U(Gamma(X, End E)):

1. There is an exact sequence of groups
   1 -> Z/n! -> pi_0 G(E) -> K^1(X) -> 1.
   The second map is the canonical map to K_1, and the kernel is central.
2. The kernel is the pullback, along the degree-one collapse to
   S^(2n) x Y, of the factorial component group.
3. For u = alpha o pr_(S^1) direct-sum 1_H and
   v = omega o pr_(S^(2n-1)) direct-sum 1_H, where alpha and omega
   generate pi_1 U(n) and pi_(2n-1) U(n), the commutator u v u* v* has
   order exactly n. So pi_0 G(E) is not abelian.
4. Adding a tautological block (X x CP^e, pr^*E direct-sum L^(direct-sum e))
   by extension by the identity is injective on pi_0, an isomorphism on
   the kernels, and pr^* on K^1.

ROUTES

gauge-components-circle-sphere-proof
