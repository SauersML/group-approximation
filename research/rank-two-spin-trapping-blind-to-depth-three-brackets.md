---
rg: 2
id: rank-two-spin-trapping-blind-to-depth-three-brackets
kind: claim
title: Spin trapping with a rank-two protected block sees no depth-three commutator, for every seed manifold
distinct_from:
  eta-squared-commutator-has-nonzero-spin-bordism-class: That shows a depth-two bracket on T^2 x S^3 is visible to spin bordism; this shows every depth-three bracket on every closed spin manifold is invisible.
  simple-cstar-unitary-components-class-four: That is the existence problem for a fourfold commutator; this rules out one detector for it, whatever the seed manifold.
---

Let M be a closed smooth spin manifold of dimension m, and let
g_1, g_2, g_3, h: M -> U(2) be smooth. Put

    f = [g_3, [g_2, [g_1, h]]]: M -> SU(2)    (pointwise commutators).

Let u in KO~^3(SU(2)) be the KO-Thom class of a point, and x = rho^* u in
KO^3(U(2)), where rho(A) = diag(det A^{-1}, 1)·A is Toms's normalization.

(a) For a depth-j nested commutator f_j of maps M -> U(2),
    f_j^* x lies in eta^j · KO^*(M). So f^* x = 0 for j = 3, since
    eta^3 = 0 in KO_3 = 0.
(b) Every Stiefel–Whitney number and every KO-characteristic number of a
    regular fibre F = f^{-1}(y), with the spin structure induced from M and
    the framing, vanishes already for j >= 1 (Stiefel–Whitney) and for
    j >= 3 (KO).
(c) Hence [M, f]_red = [F] = 0 in Omega~^Spin_m(SU(2)) ≅ Omega^Spin_{m-3},
    by the Anderson–Brown–Peterson theorem that spin bordism classes are
    determined by Stiefel–Whitney and KO-characteristic numbers. Toms's
    trapped invariant of (f o pr_M) (+) 1_Q is zero for every X and Q
    (trapped-spin-bordism-class-over-any-spin-seed-factor).

The seed manifold is arbitrary: it need not be a product of tori and spheres,
the seeds need not factor through sphere collapses, and M may carry nonzero
Pontryagin classes. This settles the "non-spherical seed manifolds" item on
simple-cstar-unitary-components-class-four negatively for spin trapping. A
detector for depth three has to see eta^3, as the lambda-mod-8 structure of
class-four-via-lambda-mod-eight-trapping-tower does. The powers eta and
eta^2 at depths one and two are Toms's example and
simple-ah-algebra-with-class-three-component-group.

The input (c) is the Anderson–Brown–Peterson detection theorem (Ann. of
Math. 86, 1967), recalled; its exact theorem number was not re-verified in
this lane. Parts (a) and (b) are proved in full in
rank-two-spin-trapping-depth-three-blind-proof. Not independently reviewed.
