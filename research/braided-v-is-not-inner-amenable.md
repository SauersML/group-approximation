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
UNREVIEWED as of 2026-09-13.

Route: `braided-v-is-not-inner-amenable-proof`.
