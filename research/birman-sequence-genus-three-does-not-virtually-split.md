---
rg: 2
id: birman-sequence-genus-three-does-not-virtually-split
kind: claim
title: In genus three the Birman exact sequence of a closed surface admits no section over a finite-index subgroup
distinct_from:
  birman-exact-sequence-does-not-virtually-split: that is Chen--Salter's Theorem A for genus at least four, stated even over finite-index subgroups of Torelli; this is genus three, over finite-index subgroups of the full mapping class group, by an adaptation of their argument.
  outer-covering-lifts-are-virtual-sections: that is the elementary equivalence between covering lifts and virtual sections in every genus; this is the non-existence of such sections in genus three.
artifacts:
  - research/artifacts/bh-birman-genus3-section-2026-09-12.md
---

**ESTABLISHED (adaptation of Chen--Salter's argument; not independently
reviewed).** Let `Σ` be a closed orientable surface of genus 3, and let
`p: Mod(Σ, ∗) → Mod(Σ)` forget the marked point. There is no finite-index
subgroup `L ≤ Mod(Σ)` with a homomorphism `σ: L → Mod(Σ, ∗)` such that
`p∘σ = id_L`.

**Why it matters.** By `outer-covering-lifts-are-virtual-sections`, the BFFHZ
one-puncture covering template for Boone--Higman is the same as a virtual section.
Chen--Salter exclude such sections from genus four on. This claim excludes them in
genus three, the one remaining closed case of that template.

**Scope.**
- **Mapping-class-group level only.** Chen--Salter's Theorem A for `g ≥ 4` also
  excludes sections over finite-index subgroups of the Torelli group. The genus-three
  proof uses twists outside Torelli in its rank bounds, so the Torelli-level
  statement in genus three is not claimed.
- **Relation to Luo--Watanabe.** arXiv:2502.14343v2, Theorem 1, read from the PDF on
  MSI, proves non-splitting in genus `≥ 3` for finite-index subgroups containing the
  Johnson kernel, both profinitely and discretely. At the discrete level this claim
  covers every finite-index subgroup.
- **Novelty.** Not searched. No source read here states the general genus-three case.

**Proof outline.** The derivation is `birman-genus-three-no-virtual-splitting-proof`,
with details in §3 of the artifact.
1. **Lemma 2.9.** Chen--Salter's version is re-proved at the mapping class group level. Rank-6 twist
   centralizers and a forget-and-restrict argument replace the bound `2g − 3 > 3`.
2. **Lemmas 2.15--2.16.** They are replaced by a one-sided `H_1` argument on the genus-2
   disk-pushing group, which gives single-curve lifts of separating twists.
3. **Placing the marked point.** Two disjoint handle curves put the marked point on
   a side of genus 2.
4. **Section 3.** Chen--Salter's Section 3 then runs with `p = 2`.
