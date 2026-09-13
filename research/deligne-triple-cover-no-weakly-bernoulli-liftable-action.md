---
rg: 2
id: deligne-triple-cover-no-weakly-bernoulli-liftable-action
kind: claim
title: No free action of Sp_4(Z) lifted across Deligne's triple cover is weakly contained in Bernoulli shifts
distinct_from:
  weakly-bernoulli-liftable-actions-force-virtual-splitting: that is the general open claim over every w-rigid base; this is its Deligne instance over Sp_4(Z), the case that decides case (i) of the finite-kernel Rokhlin ascent for E_3.
  gohla-thom-lattices-no-weakly-bernoulli-liftable-action: that proves the same kind of statement over p-adic lattices where cosystolic inequalities are known; this is the real rank-2 arithmetic case where none is known.
  deligne-triple-cover-is-sofic: that is soficity of E_3; a counterexample to this claim would prove it, while this claim could hold with E_3 sofic.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-sofic-transfer-and-sp4-2026-09-13.md
---

**OPEN.** Let `1 -> C_3 -> E_3 -> Sp_4(Z) -> 1` be Deligne's triple cover. No free p.m.p. `Sp_4(Z)`-action that is the
`C_3`-quotient of a free `E_3`-action is weakly contained in `[0,1]^(Sp_4(Z))`.

**Equivalent form.** Restrict to the torsionfree `Gamma(3)`. Then, by `bernoulli-maximizes-extension-class-norm`, the claim
holds iff the Gohla--Thom norm of the Deligne class on the Bernoulli shift of `Gamma(3)` is positive, iff that norm is
positive on some free action. Popa's theorem gives only that the class is nonzero there, not that it is
nonzero in reduced cohomology.

**Known sufficient conditions.**
- **Congruence cosystole.** A uniform lower bound on the congruence covers,
  `deligne-class-congruence-cosystole-bounded-below`, gives it through
  `deligne-weak-lift-obstruction-from-congruence-cosystole`.
- **Nonsoficity of `E_3`.** It implies this claim by `weakly-bernoulli-liftable-action-makes-extension-sofic`.

**Payoff.** Case (i) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift` would never apply to `E_3`. Only
`seward-direct-product-relative-rokhlin-entropy-conjecture` would remain as a known sufficient condition for Rokhlin
ascent to `E_3`.

## Attempts

- **Popa plus compactness (ex2-rokhlin-almost-cocycle, 2026-09-13).** It proves a positive defect for every fixed
  window and base resolution of block approximations. The claim is exactly that these defects stay bounded away from
  zero as the complexity grows. Compactness does not supply this (artifact Section 9(c)).
- **What a counterexample needs** (artifact Section 10).
  - Block approximations of unbounded complexity.
  - Torsor sofic approximations of `E_3` over every sofic approximation of `Sp_4(Z)`.
  - Cosystoles tending to 0 along every congruence chain.
  - Norm 0 on every free action.
