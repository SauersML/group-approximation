---
rg: 2
id: transvection-displacement-forces-exact-local-embedding
kind: claim
title: Rank models factoring through GL_m(F_2) with positive transvection displacement are exact local embeddings
distinct_from:
  monomial-rank-models-are-hamming-models: that turns monomial rank models into Hamming models; this forces exactness on every rank model whose stage matrices come from representations of general linear groups in which transvections displace a positive fraction, including Steinberg and other non-monomial modules.
  toeplitz-defect-dies-in-every-finite-quotient-of-el3: that concerns homomorphisms into residually finite groups; this starts from set maps into GL_m(F_2) that are exact on no relation, followed by representations, and derives exactness from transvection displacement.
artifacts:
  - research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md
---

**ESTABLISHED** (proof: Section 1 of the linked artifact, route
`transvection-displacement-local-embedding-proof`).

**Theorem.** Let `σ = lim_ω σ_k : G -> M^x` be an injective homomorphism into a characteristic-two
rank ultraproduct, with `σ_k = π_k ∘ τ_k`, where:
* `τ_k : G -> GL_(m_k)(F_2)` are set maps with `m_k >= 4`, and `π_k` are representations of
  dimension `n_k`;
* the normalized transvection displacement `d_k = rk(π_k(t) − 1)/n_k` (all transvections are
  conjugate) has `lim_ω d_k > 0`.

Then for every finite `F ⊆ G`, ω-almost every `τ_k` is an injective partial homomorphism on `F`.
So `G` is locally embeddable into finite groups (LEF).

**Key lemma.** For `z != 1` in `GL_m(F_2)` with `m >= 4`, there are transvections `u, u''` such
that `[z, u]` or `[[z, u], u'']` is a transvection. Since `rk(π([z,u]) − 1) <= 2 rk(π(z) − 1)` in
every representation, `rk(π(z) − 1) >= rk(π(t) − 1)/4`. So every relator error `z_k != 1` costs
normalized rank at least `d_k/4`.

**Where the displacement comes from.**
* **Natural assignment.** If `τ_k(g_0)` is a transvection for one fixed `g_0 != 1`, for example
  `x_13(1 − s0 t0) -> u_13(0,0)` in the natural level assignment, then
  `lim_ω d_k = rk(σ(g_0) − 1) > 0`.
* **Projective share.** If `π_k` has a projective summand of normalized dimension `>= α`, then
  `d_k >= α/2`, because an involution acts freely on a projective module. This covers Steinberg
  modules, projective indecomposables and free modules.

**Consequence for `R^x = EL_3(L_(F_2)(1,2))`.** `R^x` is infinite, simple
(`binary-leavitt-unit-group-is-simple`) and finitely presented
(`leavitt-unit-group-finitely-presented`). So it is not residually finite, hence not LEF. No
nontrivial characteristic-two rank model of `R^x` factors stagewise through representations of
general linear groups with positive transvection displacement. That excludes both sources above,
whatever `τ_k` does on non-finitary elements and near the level boundary.

**Survivors.** `d_k -> 0` along ω. Then a product of `s` transvections is displaced by at most
`s d_k`, so for each `g != 1` the element `τ_k(g)` needs unboundedly many transvections. The
identity representation (`d_k = 1/n_k`) shows that this is just the general rank-model setting.
Nothing beyond vanishing transvection displacement is excluded.

**Odd characteristic.** Over `F_q`, the lemma holds for non-central `z`. So relator errors are
forced into the centre. For `G_3 = L_(F_3)(1,2)^x`, errors of central type survive.
