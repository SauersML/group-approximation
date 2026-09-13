---
rg: 2
id: braided-v-is-not-inner-amenable
kind: claim
title: "Braided V is not inner amenable"
distinct_from:
  thompson-t-and-v-are-not-inner-amenable: that is the Haagerup–Olesen theorem about T and V; this is about Brin's braided V, which surjects onto V with a non-amenable pure braided kernel, so it does not follow from the V case
---

Brin's braided Thompson group bV (arXiv:math/0406042; V_br in arXiv:1210.2931) is not inner
amenable: no finitely additive probability measure on `bV ∖ {1}` is invariant under conjugation.

Consequences:
- bV is ICC.
- Its group von Neumann algebra `L(bV)` is a II_1 factor without property Γ, so it is not McDuff.
- Every subgroup of bV that contains a lift H of a free subgroup of the copy Λ of PSL(2,Z) in T is
  also not inner amenable.

This answers Zaremsky's Problem 2.11 negatively (root `zaremsky-2-11-braided-v-inner-amenable`).

Reviewed: PASS by z-verify-groups on 2026-09-13, §8 of
`research/artifacts/zp-review-groups-2026-09-13-part1.md` (c0ff0a5f90).

Novelty (z-status-b, 2026-09-13, `research/artifacts/zp-novelty-2-11-braided-v-inner-amenable-2026-09-13.md`,
dfbf7114a0): this answers Problem 2.11 negatively, as the list predicted, and is the first proof
within the sources checked. The check was bounded: MathSciNet and zbMATH were not searched.

Credit:
- Haagerup–Olesen: the copy of PSL(2,Z) in T and the centralizer technique.
- Rosenblatt: the stabilizer criterion.
- Effros: property Γ.
- Brin and Dehornoy: braided V.
- Bashwinger–Zaremsky: `L(bV)` is a II_1 factor.

Route: `braided-v-is-not-inner-amenable-proof`.
