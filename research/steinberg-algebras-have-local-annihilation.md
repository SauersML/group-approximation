---
rg: 2
id: steinberg-algebras-have-local-annihilation
kind: claim
title: Steinberg algebras of ample groupoids with compact infinite unit space have local annihilation
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a nonzero commutative ring and `𝒢` an ample groupoid whose unit space
`𝒢⁽⁰⁾` is compact and infinite. Then `R = A_k(𝒢)` has *local annihilation*: for every finite `F ⊆ R`, the set

```text
S_F = { s ∈ R : ∃ t ≠ 0 with t s = 0 and t f s = 0 for all f ∈ F }
```

generates `R` as a non-unital ring. In fact there is a clopen partition `V_1, …, V_r` of `𝒢⁽⁰⁾` with
`χ_(V_i) R ⊆ S_F` for every `i`, so the additive span of `S_F` is already `R`.

This is exactly the Lean predicate `GroupApproximation.Pestov91.LocalAnnihilation`
(`GroupApproximation/Pestov91/SimpleModCentre.lean`). No minimality, effectiveness or Hausdorffness is used.

Why: `F` is supported on finitely many compact open bisections `B_j`. Near each unit `x`, a small clopen `V` has
`V ∪ ⋃_j α_(B_j)(V)` missing a fixed clopen `W`, and `χ_W f χ_V = 0` then kills `F` on `χ_V R`. Proof in artifact §1.
