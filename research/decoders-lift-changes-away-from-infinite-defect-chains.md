---
rg: 2
id: decoders-lift-changes-away-from-infinite-defect-chains
kind: claim
title: Every decoder of a strict pair lifts finite output changes except along infinite chains of defect windows
distinct_from:
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that lifts output changes at configurations asymptotic to the image and shows some configurations are not; this lifts them at every configuration whose defect components near the change are finite, so sparse Garden-of-Eden occurrences are harmless, and it parametrizes all decoders of one encoder by retractions onto the image.
  strict-split-decoders-have-infinitely-many-sections: that produces many cellular sections of one decoder; this parametrizes the decoders of one encoder and locates where post-surjectivity of any of them can fail.
artifacts:
  - research/artifacts/gk3-post-surjective-decoders-2026-09-14.md
---

**ESTABLISHED** by `decoder-defect-chain-repair-proof` (elementary; no novelty claimed).

**Setting.**
- `G` is a group, `A` a finite alphabet, and `τ` an injective automaton on `A^G` with image `Y`.
- A decoder is an automaton `σ` on `A^G` with `σ∘τ = id`. A retraction onto `Y` is an automaton `r` on `A^G` with `r(A^G) ⊆ Y` and `r|_Y = id`.
- Configurations are asymptotic, `x ~ x'`, when they differ on a finite set.
- For an automaton `E` with memory `W` containing `1` and local rule `ε`, `E(x)(g) = ε((g⁻¹x)|_W)`. Let `L = {z|_W : z ∈ Y}`, and let the defect set be `D(x) = {g ∈ G : (g⁻¹x)|_W ∉ L}`.
- Put `U = W⁻¹W`, and call `h, h'` adjacent when `h' ∈ hU`.

**Theorem.**
1. **Decoders are retractions.** `σ ↦ τ∘σ` is a bijection from the decoders of `τ` onto the retractions onto `Y`, with inverse `r ↦ σ₀∘r` for any fixed decoder `σ₀`.
2. **Post-surjectivity transfers.** A decoder `σ` is post-surjective iff `E = τ∘σ` lifts changes inside `Y`: for every `x` and every `y ∈ Y` with `y ~ E(x)` there is `x' ~ x` with `E(x') = y`.
3. **Repair lemma.** Let `W` be a memory of `E = τ∘σ` containing `1`. Let `x ∈ A^G`, and let `y ∈ Y` differ from `E(x)` exactly on the finite set `F`. Suppose the connected components of `D(x) ∪ F`, under adjacency, that meet `F` are finite, with union `C`. Then `x' = y` on `C` and `x' = x` off `C` satisfies `E(x') = y`.
4. **Corollary (where post-surjectivity can fail).** Every decoder `σ` is post-surjective at every configuration `x` whose defect set has only finite components. More generally, a lift can fail only when some change site is adjacent to an infinite component of `D(x)`.
   - This covers every `x` asymptotic to `Y`, since then `D(x)` is finite. That recovers (b) of `post-surjective-decoders-convert-strict-pairs-to-dual-failures`.
   - It also covers configurations carrying Garden-of-Eden patterns at infinitely many translates, as long as the defect components stay finite. So the configurations of (e) there are no obstruction by themselves.

**Consequence for `strict-pairs-admit-post-surjective-decoders`.** The whole choice of a decoder's rule off the image language matters only at configurations whose defect set has an infinite adjacency component, i.e. along infinite chains of defect windows. Every retraction onto `Y` already lifts all other changes by repair.

**Calibration.** For the sitewise retraction `B → A` of the cross-alphabet toy in the artifact, `W = {1}` and `U = {1}`, so every component is a single site. The theorem predicts post-surjectivity everywhere, which holds.
