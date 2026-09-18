---
rg: 2
id: kun-thom-coset-field-has-no-finite-field-point-models
kind: claim
title: The generalized Bernoulli rational function field over a Kun-Thom coset space has no finite-field point models, because hashed point labels would build a sofic invariant measure that Theorem C forces to be constant along a Gamma-orbit
distinct_from:
  finite-field-point-models-give-the-rank-condition: that proves point models give the rank condition and builds them for Bernoulli fields over sofic groups; this proves that no point models exist for the coset field of an infranormal Kazhdan pair, over any coefficient field, although the group is residually finite.
  profinitely-closed-linear-coefficients-rank-condition: that builds exact periodic point models on permutation modules of separable subgroups; this shows that for the non-separable Kun-Thom subgroup not even approximate, random or non-periodic point models exist, so the non-closed regime left open there contains a case no point model reaches.
  finite-equidistributed-orbits-give-sofic-action: its model test rules out honest finite orbits in the Kun-Thom generalized Bernoulli space through the profinite closure of Gamma; this rules out every approximately equivariant finite labelling through Theorem C, with no profinite input.
  kun-thom-free-nonsofic-action: that is nonsoficity of one measure on the coset shift; this shows that every finite-field evaluation model of the coset field would produce a sofic measure there with a forbidden property.
---

**ESTABLISHED (unreviewed)** by [[kun-thom-coset-field-no-point-models-proof]].

**Theorem.** Let `Γ < G` be infranormal and not normal, with `Γ` and `G` Kazhdan and `G` sofic. An example is
the Theorem E pair of `kun-thom-free-nonsofic-action`, which is residually finite. Let `H = G/Γ`, `k` any field,
`m >= 1`, and `K_H(k) = k(x_(c,i) : c ∈ H, i <= m)` with `σ_g x_(c,i) = x_(gc,i)`.

Then `K_H(k)` has **no** finite-field point models over `G` in the sense of
`finite-field-point-models-give-the-rank-condition`. The same holds for every `G`-stable subring containing
`x_(c,1)`, `x_(c',1)` and `(x_(c,1) - x_(c',1))^(-1)` for one pair `c ≠ c'` in a common `Γ`-coset orbit
`c' ∈ Γ c`, with `c = gΓ` and `g^{-1}Γ g ⊄ Γ`.

**Named invariant.** Kun–Thom Theorem C: in every sofic p.m.p. action of `G`, the algebra `L^∞(X)^Γ` is
`G`-invariant.

**Where every point model dies.** Take the hashed labelling
`v ↦ (h(e_v(x_(c,1))))_(c ∈ H) ∈ {0,1}^H`, tensored with a sofic approximation of `G`.
- Its limit is a sofic invariant measure `μ` on `{0,1}^H` (Lemma LC).
- Theorem C makes `ω ↦ ω(gΓ)` invariant under `Γ`, so `ω(gΓ) = ω(γgΓ)` `μ`-a.e.
- But (P1) at the unit `x_(gΓ) - x_(γgΓ)` forces `e_v(x_(gΓ)) ≠ e_v(x_(γgΓ))` at every good site, and the hash
  keeps half of these disagreements.
- So the model fails at the element `(x_(gΓ) - x_(γgΓ))^(-1)` of `E`.

**Consequences.**
- **Class kill.** No certificate through `finite-field-point-models-give-the-rank-condition` can prove
  `kun-thom-coset-field-crossed-product-has-the-rank-condition`. This includes random evaluations along sofic
  approximations (B1 there), exact periodic models from finite quotients
  (`profinitely-closed-linear-coefficients-rank-condition`) and projective models (B2). The obstruction is
  independent of the characteristic and of `k`.
- **Exactness of the kill.** The same argument applied to Bernoulli fields (`H = G`, `Γ = 1`) gives nothing,
  since the trivial group has no nonconstant invariant coordinate. The Bernoulli case is exactly where
  point models exist (B1).
- **Characteristic 0 escapes by measure, not by points.** Over `Q`, the rank condition still holds by the
  invariant iid measure on complex embeddings (Corollary 3 of
  `coset-field-rank-failure-gives-relative-bernoulli-deficit`). That measure is not sofic, which is
  consistent with Theorem C. In characteristic `p` there is no substitute in the graph.
