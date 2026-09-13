---
rg: 2
id: simple-rings-with-local-matrix-models-are-matricial
kind: claim
title: A simple unital ring with exact unital local matrix models on exhausting finite windows embeds in an algebraic matrix ultraproduct
distinct_from:
  lef-simple-rings-are-not-finitely-presented: that shows a finitely presented simple LEF ring is finite; this is the embedding lemma making exact local models of any simple ring automatically faithful.
  minimal-subshift-algebra-is-simple-lef-ring: that builds one simple LEF ring and checks faithfulness by hand; this removes faithfulness bookkeeping for every simple ring.
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `R` be a simple unital ring and `W_1 ⊆ W_2 ⊆ ...` finite subsets
with union `R`. Let `ψ_n : R -> M_(N_n)(k)` be maps with `N_n >= 1` and `ψ_n(1) = 1`, such that
`ψ_n(a+b) = ψ_n(a) + ψ_n(b)` and `ψ_n(ab) = ψ_n(a) ψ_n(b)` whenever `a, b ∈ W_n`. Then
`Ψ = [ψ_n]_ω : R -> ∏_ω M_(N_n)(k)` is an injective unital ring homomorphism, for every non-principal
ultrafilter `ω`.

**Model test.** `R = k × k` with a coordinate projection: `R` is not simple, and the conclusion fails.

Route: `simple-rings-with-local-matrix-models-are-matricial-proof`.

**Review (un-verify-measure, 2026-09-13): PASS.** Proof re-derived; model test checked. See `research/artifacts/un-review-measure-2026-09-13-part1.md` §M1.
