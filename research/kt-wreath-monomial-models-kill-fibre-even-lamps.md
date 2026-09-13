---
rg: 2
id: kt-wreath-monomial-models-kill-fibre-even-lamps
kind: claim
title: Every monomial Hilbert--Schmidt model of the Kun--Thom wreath kills a nonzero fibre-even lamp, so partly-soft models do not exist
distinct_from:
  block-monomial-coordinate-collapse: that excludes block-monomial models in which every lamp is diagonal; this handles models whose diagonal lamps are only a submodule, and shows every block-size-one model is non-injective on the fibre-even lamps.
  block-monomial-hs-models-sofic-mod-amenable-soft-kernel: that proves a general group is sofic modulo the soft kernel of such a model; this computes what the soft kernel must contain for the Kun--Thom wreath and shows the model cannot be faithful on it.
  kt-double-admits-no-bounded-block-monomial-hs-model: that is the double, where trivial amenable radical settles every bounded block size at once; this is the wreath, which is abelian-by-sofic, so the soft-kernel split alone says nothing and Kun--Thom 4.1 has to be applied to the soft lamps.
  kun-thom-wreath-sofic-radical-is-fibre-parity-kernel: that is the group-level sofic radical; this reads it through the permutation part of a monomial model and adds a model-level non-injectivity theorem.
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md
---

**ESTABLISHED** (unreviewed).  Let `Gamma = EL_r(R_+) < G = EL_r(R) x| SL_d(Z)`
be the Kun--Thom Theorem E pair (`r, d >= 3`, any `q`), `N = EL_r(R)`,
`P = F_2[G/Gamma]`, `W = P x| G`, and `K_even <= P` the fibre-even
configurations over `G/N`.  A monomial HS model is a homomorphism
`rho : W -> prod_omega (U(1) wr S_n)` into the tracial ultraproduct of
monomial unitaries.  No trace condition is assumed.

1. **Soft lamps.**  In every block-monomial model, of any block size, the
   permutation part kills `K_even`.  For block size `1`, `rho(K_even)` is
   diagonal.
2. **An invariant soft configuration.**  Let `s in SL_d(Z)` have positive
   entries and `h = e_12(x_1^(-1))`.  The coset `s^(-1) h Gamma` has a finite
   `Gamma`-orbit `O` in the fibre of the `Gamma`-fixed coset `s^(-1) Gamma`.
   So `u = 1_O`, plus `e_(s^(-1) Gamma)` when `|O|` is odd, is a nonzero
   `Gamma`-invariant element of `K_even`.
3. **Theorem.**  For every monomial HS model `rho`, every conjugate
   `Gamma'` of `Gamma`, every `Gamma'`-invariant `v in K_even` and every
   `n in N`, `rho(n.v) = rho(v)`.  With `v = u` and `n.u != u`, the element
   `u + n.u` is a nonzero element of `K_even ∩ ker rho`.

**Corollaries.**
- No monomial HS model of `W` is injective.  `W` has no regular monomial HS
  model, and, through `diagonal-normalizer-rigidity`, no regular HS
  microstates that approximately normalize a full masa.
- Partly-soft models, with the soft lamps a proper submodule `U` and
  `K_even <= U < P`, do not exist.  This settles the model test left open on
  `monomially-hyperlinear-groups-are-sofic`: the claim predicts no regular
  monomial model of `W`, and there is none.
- For Question 3.4, the Kun--Thom wreath is fenced like the binary Leavitt unit
  group and the `q = 2` double: any hyperlinear model of `W` is
  frame-incoherent (`hyperlinear-implies-sofic-via-frame-extraction`).

**Why it works.**  Conjugating a diagonal by a monomial acts by the
permutation part exactly, whatever the phases.  So the soft lamps and the
permutation part `psi` form a covariant pair.  After tensoring `psi|G` with a
sofic representation of `G`, part 2 of
`normal-closure-fixes-gamma-fixed-algebra` (Kun--Thom 4.1) makes `N` act
trivially on every `Gamma`-fixed diagonal element.  What was missing was a
`Gamma`-fixed element among the soft lamps.  The finite orbits of item 2 are
that element.  They exist because `Gamma` compressed by a positive
substitution commensurates enough of `Gamma` conjugated by a Laurent
elementary matrix.

**Scope.**
- The trust surface of arXiv:2608.06222 travels with this claim through
  `normal-closure-fixes-gamma-fixed-algebra` and `kun-thom-nonsofic-wreath`.
- Block size `k >= 2` is not covered: the covariance identity fails inside
  blocks.
- Intermediate coset wreaths are not covered.
- Nothing here says `W` is not hyperlinear.

Derivation: `kt-wreath-monomial-models-kill-fibre-even-lamps-proof`.
