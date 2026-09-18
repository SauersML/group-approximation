---
rg: 2
id: z-localizations-embed-in-gl-n-only-along-inclusion-proof
kind: route
title: Proof via the local ring Z_(q) at a prime of P outside P'
target: z-localizations-embed-in-gl-n-only-along-inclusion
requires:
  - infinitely-q-divisible-dvr-matrices-are-torsion
---

Suppose `ι: Z[1/P] -> GL_N(Z[1/P'])` is injective and `q in P \ P'`. Every
denominator in `Z[1/P']` is prime to `q`, so `Z[1/P'] ⊆ Z_(q)`, the local ring at
`q`. So `ι` lands in `GL_N(Z_(q))`.
- `Z_(q)` is a discrete valuation ring with fraction field `Q`, maximal ideal
  `q Z_(q)` and residue field `F_q`.
- `g = ι(1)` has the roots `ι(1/q^j)` of order `q^j` for every `j`, all inside
  `GL_N(Z_(q))`.
- By `infinitely-q-divisible-dvr-matrices-are-torsion`, `g` has finite order.
- But `1` has infinite order in `Z[1/P]` and `ι` is injective, a contradiction.

So `P ⊆ P'`.

For the consequence with `n >= 2`:
- **Only if.** `GL_n(Z[1/P])` contains `Z[1/P]` as the unipotent matrices
  `[[1,x],[0,1]]` (in the top-left block), so an embedding forces `P ⊆ P'`.
- **If.** For `P ⊆ P'` and `N >= n`, the inclusion `Z[1/P] ⊆ Z[1/P']` and a
  block embedding give `GL_n(Z[1/P]) <= GL_N(Z[1/P'])`. ∎
