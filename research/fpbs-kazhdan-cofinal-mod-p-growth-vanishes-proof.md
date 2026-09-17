---
rg: 2
id: fpbs-kazhdan-cofinal-mod-p-growth-vanishes-proof
kind: route
title: Shrink cocycle support through Frattini covers and coprime descents until it violates the Kazhdan support bound
target: fpbs-kazhdan-cofinal-mod-p-growth-vanishes
requires:
  - fpbs-shalom-property-t-is-open
  - fpbs-lackenby-cocycle-support-toolkit
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

Written deduction, lane `sw-007`, 2026-09-17. The full argument is Section
"Theorem B" of the artifact.

1. **Kazhdan support bound.** Pass to a finitely presented Kazhdan cover `G`
   with Kazhdan pair `(X,kappa)`. Every nonzero class in `H^1(K_U;F_p)`, for
   every finite cover `K_U` of the presentation complex, has relative size at
   least `kappa^2/(4|X|)`. Proof: the zero level set of the lifted cocycle in
   the `p`-fold cover has boundary inside the lifted support. It is a
   `1/p`-fraction set, so (T) forces a boundary of size `kappa^2 N/4`.
2. **Invariant.** Carry a good subgroup `A`: linear growth
   `d_p(pi A) >= c[G:A]`, plus `u = ceil(2|R|/c)` independent classes on
   `K_A` with support fraction `sigma`.
3. **Frattini cover.** Pass to `B = pi^(-1)Phi_p(pi A)`. Lackenby's Theorem 5.1
   gives more than `u` independent classes supported over the old support.
   Theorem 6.1 selects `u` of them with support fraction at most
   `theta_u sigma`, where `theta_u < 1`.
4. **Coprime descent.** Pick a member `N` of the family inside `Phi_p(pi A)`,
   and let `A'` be the preimage of a Sylow `p`-subgroup of `Phi_p(pi A)/N`.
   Restriction to `A'` is injective by transfer and keeps the support fraction.
5. **Growth inherited.** Lemma 3.3 applied to `N`, normal of `p`-power index
   in `A'`, gives `d_p(pi A') >= c[G:A']`. So `A'` is good.
6. **Contradiction.** After `m` steps with `theta_u^m < kappa^2/(4|X|)`, the
   bound in step 1 is violated.

Calibration: with Lackenby's Theorem 4.1 in place of step 1, the same iteration
shows that a finitely presented group with a profinitely cofinal normal family
of linear mod-`p` growth is large. This agrees with Lackenby's Theorem 1.6
(positive first `L^2`-Betti number implies large) and with the free group.
