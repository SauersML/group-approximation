---
rg: 2
id: sl3z-lattice-space-action-is-not-sofic
kind: claim
title: The action of SL3(Z) on the space SL3(R)/SL3(Z) of unimodular lattices in R^3 is not sofic
refuted_by:
  - sl3z-lattice-space-action-is-sofic
distinct_from:
  sl3z-admits-nonsofic-action: that asks for some nonsofic action of SL3(Z); this names one explicit free mixing candidate, the canonical coupling action, whose failure would answer that claim and the mixing root at once
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that concerns SL3(Z[1/2]) on a compact quotient of the p-adic group SL3(Q_2), where SL3(Z) acts profinitely; this is the real place, where SL3(Z) acts mixingly on a non-compact homogeneous space
  induced-actions-sofic-iff-homogeneous-action-sofic: that proves soficity of this action controls every induced action; this asks whether it fails
---

**REFUTED (unreviewed).** `sl3z-lattice-space-action-is-sofic` proves that the action is sofic. The
Hecke orbits `SL_3(Z)·a^(−1)SL_3(Z)`, `a ∈ SL_3(Z[1/p])`, are finite. Mixing of `SL_3(Q_p)` on the
S-arithmetic cover makes them equidistribute, and through
`finite-equidistributed-orbits-give-sofic-action` they give finite models. The original two-sided
statement follows.

**Original statement (formerly OPEN, two-sided).** Let `X_3 = SL_3(R)/SL_3(Z)`, the space of unimodular
lattices in `R^3`, with its `SL_3(R)`-invariant probability measure, and let `SL_3(Z)` act by left
multiplication, `γ·L = γL`. Claim: this p.m.p. action is **not sofic** (Păunescu Definition 1.4).

The action is essentially free (`induced-actions-sofic-iff-homogeneous-action-sofic`, freeness paragraph
of its proof). It is mixing, because `SL_3(R) ↷ X_3` is transitive, hence ergodic, and Howe--Moore holds
(`howe-moore-property-for-simple-lie-and-p-adic-groups`). `SL_3(Z)` is residually finite, hence sofic.
So a proof of the claim would answer both `sl3z-admits-nonsofic-action` and
`mixing-free-nonsofic-action-of-sofic-group` with one explicit action. A disproof is the calibration of
`induced-actions-sofic-iff-homogeneous-action-sofic`: induction through `SL_3(R)` would then map sofic
seeds to sofic actions.

**Model test.** The rank-one analog is false. `SL_2(Z) = Z/4 *_(Z/2) Z/6` is an amalgam of finite
groups over a finite group, so it lies in Păunescu's class (Theorem 3.9,
`paunescu-sofic-action-class-permanence`), and `SL_2(Z) ↷ SL_2(R)/SL_2(Z)` is sofic. Any argument for the
claim must use higher rank.

## Attempts

* **Kun--Thom Theorem C.** Dead: the action is mixing, so every infinite subgroup acts ergodically
  (`kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions`).
* **Kun--Thom Theorem 4.1 on the embedded crossed product.** Dead:
  `permutation-centralizer-blind-to-weakly-mixing-actions`.
* **Soficity through weak containment.** An action weakly contained in a sofic action is sofic (Alpeev,
  arXiv:1706.01864, p. 2: *"It is a folklore fact that an action weakly contained in the sofic action is
  sofic itself."*). The natural target is the Bernoulli shift of `SL_3(Z)`. But weak containment in
  Bernoulli forces the Koopman representation on `L²_0(X_3)`, restricted to `SL_3(Z)`, to be weakly
  contained in the regular representation. For cusp forms that is an archimedean Ramanujan-type bound,
  not known for `SL_3(Z)`. Even granted, temperedness does not give weak containment of actions. Dies
  at: no criterion turning spectral data into weak containment of actions.
* **p-adic analogs.** On a compact quotient `SL_3(Q_p)/Λ'` by a cocompact lattice, `SL_3(Z)` acts
  through the compact open `SL_3(Z_p)`. Its orbits are `SL_3(Z_p)` modulo finite stabilizers, so the
  action is an inverse limit of finite actions and sofic (Alpeev Lemma 4.3: *"Inverse limit of sofic
  actions is sofic."*). The real place, where the action is mixing and non-compact, is the essential case.
* **Other lattices of `SL_3(R)`.** For a lattice `Λ`, `SL_3(Z) ↷ SL_3(R)/Λ` has the same status as
  `Λ ↷ SL_3(Z)\SL_3(R)`, by the coupling `SL_3(R)` and `sofic-free-actions-are-soe-invariant`.
  Cocompact `Λ` from a division algebra of degree `3` give compact homogeneous spaces; whether they are
  easier is unexplored.
* **Hecke orbits (the refutation).** The commensurator `SL_3(Q)` is dense, and its points are exactly
  the points of `X_3` with finite orbit. The p-adic mixing of the previous bullet, pushed through the
  cover `(SL_3(R) × SL_3(Q_p))/SL_3(Z[1/p])` and thickened in the real factor, equidistributes these
  orbits in `X_3`. For `Λ` not commensurable with `SL_3(Z)`, no orbit on `SL_3(R)/Λ` is finite, so the
  previous bullet is where Hecke orbits cannot reach (part 2 artifact of
  `sl3z-lattice-space-action-is-sofic`, Section 8).
