---
rg: 2
id: jones-subgroup-coamenable-from-extensive-amenability-proof
kind: route
title: An invariant mean for the dyadic lamplighter restricts along the parity cocycle to the coset space of Jones' subgroup
target: jones-subgroup-coamenable-if-dyadic-action-extensively-amenable
requires: [jones-subgroup-cosets-form-a-parity-lamplighter, affine-lamplighter-amenable-iff-extensively-amenable]
artifacts:
  - research/artifacts/ideas-wildcards-2026-09-14.md
---

1. **The lamplighter mean exists.** `F` acts transitively on `D`: two leaf subdivisions with equally many
   leaves give an element of `F` matching any two chosen leaf endpoints. By the cited criterion, extensive
   amenability gives an invariant mean `m` on `P_f(D)` for the affine action `(A,g)·E = A Δ gE` of `P_f(D) ⋊ F`.
2. **It restricts along the cocycle.** `g ↦ (J_L(g), g)` is a homomorphism `F → P_f(D) ⋊ F`, and the pulled-back
   action is `⋆` (`jones-subgroup-cosets-form-a-parity-lamplighter`, item 3). So `m` is `⋆`-invariant.
3. **It lands on the coset space.** `⋆` is transitive with stabilizer `\vec F` (item 4), so `m` is an `F`-invariant
   mean on `F/\vec F`. That is co-amenability, equivalently `1_F ≺ λ_(F/\vec F)` (Eymard; also stated in
   Aiello–Brothier–Conti, arXiv:1901.10597, Remark 4.7).
4. **Contrapositive.** The contrapositive and the cited Lemma 2.1 (actions of amenable groups are extensively
   amenable) give the chain in the claim.
