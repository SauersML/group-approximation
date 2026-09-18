---
rg: 2
id: cantor-central-witnesses-have-long-range-dependence
kind: claim
title: "Class-kill for central non-rigidity of C(C,Z) ⋊ V: in any witness spectral law, the phases of two disjoint non-complementary cones stay TV-dependent (at least about 1/8, also conditionally on any V-invariant function), so no mixing, finite-range or independent-subtree random character witnesses failure of relative (T) for <1_C>"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that is the full relative (T) statement; this only kills the class of witness laws with a nearly independent pair of cone phases
  extractable-character-spectra-carry-no-almost-invariant-vectors: that kills laws on characters with an equivariant extraction to Prob(C) (via a paradoxical push-forward); this kills laws by their dependence structure, with no hypothesis on the characters themselves, and so reaches scale-incoherent characters
  cantor-integer-maps-central-growth-criterion: that reduces central growth to almost-invariant laws with χ(1_C) ≠ 1; this constrains the joint law of any such witness
  cantor-integer-maps-pair-lacks-relative-property-t: that builds witnesses for (G, C(C,Z)) from Bernoulli cone products, which are nearly independent across disjoint cones; this shows such near-independence is exactly what cannot survive once χ(1_C) ≠ 1
---

**Setting.** `C = {0,1}^N`, `A = C(C,Z)`, `G = A ⋊ V`, `T = R/Z` written additively.
A character `χ ∈ Â = Hom(A,T)` is written on clopens as `χ[U] = χ(1_U)`, and `V` acts by
`(g·χ)[U] = χ[g^{-1}U]`. The phase `λ(χ) = χ[C]` is `V`-invariant. For `g ∈ V` and a
probability `μ` on `Â`, `g_*μ` is the push-forward along `χ ↦ g·χ`, and
`d(μ,ν) = sup_B |μ(B) − ν(B)|`.

**Theorem.** Let `u, v` be finite words with `[u] ∩ [v] = ∅` and `[u] ∪ [v] ≠ C`. Fix
`g, g_u, g_v ∈ V` with `g[u] = [00]`, `g[v] = [01]`, `g_u[u] = [0]`, `g_v[v] = [0]`, and let
`h_3` be the first-letter swap. Let `F = {g, g_u, g_v, h_3}`. Let `μ` be a probability on `Â`,
`f : Â → Y` a `V`-invariant Borel map to a standard Borel space (for example constant, or
`f = λ`), `μ = ∫ μ_y dρ(y)` its disintegration, and
`α_y = d(law_{μ_y}(χ[u], χ[v]), law_{μ_y}χ[u] ⊗ law_{μ_y}χ[v])`, `ᾱ = ∫ α_y dρ`. Then

`μ(χ[C] ≠ 0) ≤ ∫ |e^{2πiχ[0]} − 1| dμ + 25 Σ_{k∈F} d(k_*μ, μ) + 8ᾱ.`

**Corollary (witnesses).** Let `S` be a finite generating set of `G` containing `1_{[0]}`, and
let `π` be a unitary representation of `G` with no nonzero `π(1_C)`-invariant vector. Let `ξ` be
a unit vector with `‖π(s)ξ − ξ‖ ≤ ε` for `s ∈ S`, and `μ` its `A`-spectral law. Then, for every
admissible `(u, v, F)` as above and every invariant `f`,

`ᾱ ≥ (1 − ε − 50 L ε)/8`, where `L = Σ_{k∈F} |k|_S`.

So along any sequence witnessing failure of relative (T) for `(G, Z·1_C)` (with `ε → 0`), every
admissible pair of cones whose moving elements have word length `o(1/ε)` keeps conditional
TV-dependence at least `1/8 − o(1)`.

**Class killed.** Witness laws in which some such pair of cone phases is nearly independent,
unconditionally or given any `V`-invariant function (for example the central phase `λ`).
This includes:
- independent random data attached to disjoint subtrees;
- finite-range dependent or α-mixing random characters, once the mixing scale is `o(1/ε)` in
  word length;
- wrapped Gaussian random charges whose correlation between some admissible pair of cones is
  below `1/5` (Pinsker gives `α ≤ |ρ|/(2√(1−ρ²))`);
- products of cone characters over independent random word sets, whenever the common
  prefixes of `u` and `v` are included with total probability `q < 1/25`. Given those
  indicators the two phases are independent, so `α ≤ 3q`.

- **Invariant:** the self-convolution identity `1_{[0]} = 1_{[00]} + 1_{[01]}`. With
  independence, two prefix moves give `ν ≈ ν * ν` in total variation for the law `ν` of `χ[0]`.
- **Where every member dies:** the Fourier atom lemma. `ν̂(m)` stays near `{0, 1}`, moves by
  less than `1` per step in `m`, and starts at `ν̂(0) = 1`. So `ν̂ ≈ 1` everywhere, `ν` has an
  atom of mass near `1` at `0`, and the same holds for `χ[1]`. That forces `χ[C] = 0`, which
  contradicts the missing `1_C`-invariant vectors.
- **Survivors:** laws in which every admissible pair of cone phases is strongly dependent, with
  dependence not explained by any `V`-invariant function. Scale-incoherent characters with
  global, wrap-around coupling are not touched.

Proof: `cantor-central-witnesses-have-long-range-dependence-proof`.
