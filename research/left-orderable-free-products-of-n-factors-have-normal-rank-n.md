---
rg: 2
id: left-orderable-free-products-of-n-factors-have-normal-rank-n
kind: claim
title: A free product of n nontrivial left-orderable groups has normal rank at least n
distinct_from:
  left-orderable-free-products-have-normal-rank-above-one: that gives the lower bound 2 for two or more nontrivial left-orderable factors; this asks for the lower bound n with n factors.
---

**OPEN.** The source is Chen–Lodha, arXiv:2510.26073 v2, `wiegold.tex`.
- **l.269–271, Question:** "Let G be a free product of n nontrivial
  left-orderable groups. Is the normal rank of G at least n?"
- **l.272:** "A positive answer would imply that the connected sum of n
  3-manifolds with nontrivial left-orderable fundamental groups must have Dehn
  surgery number at least n."

**Settled cases.**
- **`n = 2`:** `left-orderable-free-products-have-normal-rank-above-one`.
- **Factors mapping onto `Z`:** if every factor maps onto `Z`, then `G^ab` maps onto
  `Z^n`, so the normal rank is at least `n`. The question is therefore about
  factors with small abelianization, such as perfect ones.

## Attempts

1. **Reduction by quotients** (solve-wiegold, 2026-09-13). Killing factors, or
   passing to left-orderable quotients of factors, preserves normal generation,
   but it only lowers the number of factors. This way the two-factor theorem gives
   only the bound 2.
   - A proof of the bound 3 for three perfect factors needs a two-relator version
     of Theorem B.
   - The Chen–Lodha surface argument builds a planar surface from one relator
     (`k+1` boundary components, degree at least `k`; source l.1454–1464).
   - With two relators the boundary components carry two different words, and
     their spectral gap theorem is stated for a single `w`.
