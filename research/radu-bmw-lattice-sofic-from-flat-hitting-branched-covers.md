---
rg: 2
id: radu-bmw-lattice-sofic-from-flat-hitting-branched-covers
kind: route
title: Hyperbolize Radu's square complex by sparse girth-branching, then induce from residually finite cubulated covers
target: radu-bmw-lattice-sofic
requires:
  - radu-square-complex-flat-hitting-sparse-branched-covers
  - flat-hitting-branched-covers-have-hyperbolic-pi1
  - sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
  - hyperbolic-cubulated-groups-are-residually-finite
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - sofic-kernel-amenable-quotient-permanence
---

**OPEN (one open prerequisite).**  Everything except the combinatorial
existence statement `radu-square-complex-flat-hitting-sparse-branched-covers`
is established.

1. Take covers `X_k -> S_R` with `beta(X_k) -> 0`, satisfying (G) and (H),
   from the open prerequisite.
2. By `flat-hitting-branched-covers-have-hyperbolic-pi1`, each `pi_1(X_k)`
   is a hyperbolic group acting properly and cocompactly on the CAT(0) cube
   complex `X_k~`.  So it is residually finite
   (`hyperbolic-cubulated-groups-are-residually-finite`), hence sofic.
3. By part 1 of `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`,
   `pi_1(S_R)` is sofic.
4. `pi_1(S_R)` has index four in `Gamma_R`
   (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`).  Finite-index
   permanence (`sofic-kernel-amenable-quotient-permanence`, applied to the
   normal core) makes `Gamma_R` sofic.

In step 3 the residual finiteness of `pi_1(X_k)` gives the model directly.
The model set is `Lambda_k / N_k x p^(-1)(v)`, for a finite quotient
`Lambda_k / N_k` in which the finite set `E` injects, so no sofic
approximation of `Lambda_k` is needed.

**Kill condition.**  This route dies exactly when sparse girth-branching can
never make every flat grid of `T_3 x T_3` pass through a branch point.  A
nonsoficity proof for `Gamma_R` would prove that, so any construction
failure should be recorded as that obstruction.
