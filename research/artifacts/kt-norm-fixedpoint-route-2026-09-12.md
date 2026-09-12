# Kun–Thom Theorem 4.1 in Lean: the fixed-point lane

Lane `kt-norm-fixedpoint`, 2026-09-12. Part of the Bowen–Chapman Problem 1.1
formalization: Kun–Thom, arXiv:2608.06222v3, Theorem 4.1 must be proved in
Lean, with no literature input, for the explicit pair of the campaign.

## 1. The fixed-point algebra does not reach the commutant

Kun–Thom §3 (Proposition 3.1 / Theorem C) shows that each compressor
`t ∈ P_Γ` carries the `Γ`-components of a sofic approximation onto
`Γ`-components up to `o(|Y_n|)`. The mechanism: the component-size function
normalized by the ambient median, one-sided under `t`, a permutation
conserves its sum, and ambient expansion pins it at `1/2`.

That is normalization of the diagonal fixed-point algebra. It does not give
the permutation centralizer. If `q` almost commutes with `σ(Γ)` and
`c = u q u⁻¹` with `u` representing `σ(t)`, then `c` and `σ(γ) c σ(γ)⁻¹`
induce the same permutation of `Γ`-components, so the commutation defect of
`c` lives inside components. Only the isotropy and orbit counting of §4
detects it (also found independently by lane `kt-norm-counting`).

Consequence: this lane contributes to the §4 route. The median layer already
on main (`Matching/MedianNormalization`, `NormalizedVariation`,
`GlobalVariation`, `Pinning`) covers the §3 estimate.

## 2. Free versus injective representations

Kun–Thom's sofic representations are free: `tr σ(g) = 0` for `g ≠ 1`. The
landed `HasSoficCentralizerNormalization` quantifies over all injective `ρ`.
The campaign therefore retargeted to the free sequential Prop
`HasSequentialCentralizerNormalization`, owned by lane `kt-norm-repo`.

A reduction from the sequential Prop to the landed injective Prop exists, and
is parked because the endpoint does not need it:
* principal ultrafilter: the ultraproduct is a quotient of `Perm (X n₀)`, so a
  finite infranormal image is normal;
* nonprincipal ultrafilter: tensor `ρ` with a free sofic approximation on a
  diagonal subsequence, and take `v_k = q̃_{n_k} ⊗ 1`. Then `[a ⊗ 1, b ⊗ c]`
  has the Hamming length of `[a, b]`.

## 3. This lane's piece: from a bisection back to a permutation (gap 4)

Kun–Thom's proof of 4.1 ends by patching the arrows of a total bisection of
the cluster groupoid `C_n` into a permutation `b̂_n`, and bounding
`d_H(b̂_n, u_n â_n u_n⁻¹)`. The converse in their Lemma 4.2(4) says a patched
bisection of allowed arrows lies in the centralizer.

Finite module `GroupApproximation/KunThom/FixedPointNormalizationPatching.lean`
(namespace `GroupApproximation.BlockPatching`):
* `BlockEmbedding Y I`: pairwise disjoint blocks inside a finite model;
  `BlockArrows E`: a block permutation with one `FinitePartialBijection`
  arrow per block; `BlockAction E L`: a block-preserving labelled action.
* `BlockArrows.patch`: the arrows glued and extended to a permutation, with
  `patch_embed`.
* `card_domain`: the glued domain has the total source mass.
* `card_hammingDisagreement_patch_le`:
  `#{y | patch y ≠ w y} ≤ #(univ \ domain) + #arrowDisagreement w`.
* `card_commutationDefect_patch_le`: `#{y | patch (a_s y) ≠ a_s (patch y)}`
  is at most `2·#(univ \ domain)` plus the total equivariance defect of the
  arrows.

Next, once the relative functor (`kt-norm-repo` / `kt-norm-counting`) and the
cluster data (`kt-norm-paper`) fix their shapes: the matched-overlap estimate
comparing `b̂_n` with `u_n â_n u_n⁻¹` (tex, lines 1314–1344), and its sequential
`Vanishing` form.
