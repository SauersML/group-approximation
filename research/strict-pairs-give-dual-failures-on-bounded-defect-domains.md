---
rg: 2
id: strict-pairs-give-dual-failures-on-bounded-defect-domains
kind: claim
title: Every decoder of a strict pair is strongly post-surjective and not pre-injective on the proper strongly irreducible SFT of configurations with small defect components
distinct_from:
  decoders-lift-changes-away-from-infinite-defect-chains: that locates where a decoder can fail post-surjectivity on the full shift; this cuts the domain down to the subshift where the failure locus is empty, proves the lifts stay inside it, and proves that subshift is a proper strongly irreducible SFT on which the decoder is still not pre-injective.
  strict-pairs-admit-post-surjective-decoders: that asks for a decoder post-surjective on the whole full shift, which needs a choice of rule off the image language; this needs no choice, since every decoder is post-surjective on the bounded-defect domain.
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that converts a strict pair with a full-shift post-surjective decoder into a dual failure on the full shift; this produces a dual failure from a proper subshift domain onto the full shift, for every strict pair and every decoder.
artifacts:
  - research/artifacts/bounded-defect-domain-duality-2026-09-17.md
---

**ESTABLISHED** by `bounded-defect-domain-dual-failure-proof` (elementary; no novelty claimed for the
individual steps, which extend the repair lemma).

**Setting.** As in `decoders-lift-changes-away-from-infinite-defect-chains`.
- `G` is a group, `A` a finite alphabet, `(τ, σ)` a strict pair on `A^G` with image `Y = τ(A^G) ⊊ A^G`.
- Put `E = τ∘σ`, a retraction onto `Y`.
- Fix a finite `W ∋ 1` that contains a memory set of `E` and a memory set `M` of `τ`. Put `L = {z|_W : z ∈ Y}`.
- The defect set of `x` is `D(x) = {g : (g⁻¹x)|_W ∉ L}`. Here `(g⁻¹x)(w) = x(gw)`.
- Put `U = W⁻¹W`. Sites `h, h'` are adjacent when `h' ∈ hU`.
- For `R ≥ 1`, let `X_R` be the set of `x ∈ A^G` all of whose adjacency components of `D(x)` have at most `R` elements.

A map `F : X → A^G` on a subshift `X` is **strongly post-surjective** if there is a finite `Φ ⊆ G` with the
following property. For every `x ∈ X` and every `z ~ F(x)` there is `x' ∈ X` with `x' ~ x`, `F(x') = z`, and
`Δ(x, x') ⊆ Δ(F(x), z)Φ`. This is the Doucha–Gismatullin notion, with lifts required to stay in `X`. `F` is
**pre-injective on `X`** if distinct asymptotic points of `X` have distinct images.

**Theorem.** For every `R ≥ 1`:
1. **Domain.** `X_R` is a subshift of finite type. It contains `Y`, and it is strongly irreducible.
2. **Post-surjectivity.** The restriction `σ|_{X_R} : X_R → A^G` is strongly post-surjective, with `Φ = M⁻¹U^R`.
3. **Surjectivity with a section.** `σ|_{X_R}` is surjective, and `τ : A^G → Y ⊆ X_R` is an automaton right inverse.

Now fix a pattern `p` on a finite `P` that occurs in no point of `Y` (one exists because `Y` is closed and proper).
4. **Non-pre-injectivity.** If `R ≥ |P||W|`, then `σ|_{X_R}` is not pre-injective.
5. **Properness.** If `W ⊇ PP⁻¹P`, then `X_R ≠ A^G` for every `R`.

With `W ⊇ PP⁻¹P ∪ M ∪ {1}` together with a memory of `E`, and with `R ≥ |P||W|`, all five hold at once.

**Corollary (per group).** If a group `G` carries a strict pair, then `G` carries a proper strongly irreducible
SFT `X ⊊ A^G` and an automaton `F : X → A^G` that is strongly post-surjective and not pre-injective, over the
same alphabet `A`. So every group satisfying `proper-sft-domains-admit-no-dual-failures` is surjunctive.

**What this changes.** The decoder-choice problem of `strict-pairs-admit-post-surjective-decoders` exists only
because the domain was required to be the whole full shift. On the bounded-defect domain every decoder already
works.
- The only information lost is at configurations with a large or infinite defect component.
- Those are exactly the configurations the repair lemma cannot handle.
- The old hole is equivalent to extending some `σ|_{X_R}` to the full shift while keeping post-surjectivity.
