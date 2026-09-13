---
rg: 2
id: torsion-free-free-products-have-normal-rank-above-one
kind: claim
title: A free product of two nontrivial torsion-free groups is never the normal closure of one element
distinct_from:
  left-orderable-free-products-have-normal-rank-above-one: that proves this for left-orderable factors, and for factors admitting nontrivial left-orderable quotients; this asks it for every pair of torsion-free factors.
  klyachko-kl-holds-for-torsion-free: that settles the case B = Z for relators of exponent sum ±1, through the torsion-free Kervaire--Laudenbach theorem; this has two arbitrary torsion-free factors and no exponent-sum handle.
---

**OPEN.** The source is Chen–Lodha, arXiv:2510.26073 v2, `wiegold.tex`.
- **l.224:** Theorem B "was known to be true under the much stronger assumption
  that each free factor is locally indicable [...]; see the independent work of
  Brodskiĭ [...], Howie [...] and Short [...]."
- **l.225:** "Theorem B is also suspected to hold under the weaker assumption that
  each free factor is torsion-free; see Kirby's (1970s) problem list [Kir78,
  Problem 66] contributed by Freedman. Such generalizations are challenging due
  to the lack of structures."

The primary Kirby list was not read. The PDF at the URL in their bibliography was
fetched on MSI, but text extraction gave no matching lines, and it was not
inspected further.

**Settled cases.**
- Locally indicable factors: Brodskiĭ, Howie and Short, per l.224.
- Left-orderable factors, and factors with nontrivial left-orderable quotients:
  `left-orderable-free-products-have-normal-rank-above-one`.
- `B = Z`: `klyachko-kl-holds-for-torsion-free` (exponent sum must be `±1`, which
  normal generation forces).

**Why torsion-freeness is needed.** `coprime-order-normal-generators-give-normal-rank-one`
gives normal rank one as soon as the factors have normal generators of coprime
finite orders.

## Attempts

1. **Quotient constraints** (solve-wiegold, 2026-09-13; established in
   `normal-rank-one-free-products-need-cyclic-abelianization`). Any counterexample
   `A * B` has two properties:
   - `A^ab ≅ Z/m` and `B^ab ≅ Z/n` with `gcd(m,n) = 1` (possibly trivial);
   - at least one factor has no nontrivial left-orderable quotient.

   So the first cases to test are torsion-free groups with finite abelianization
   and no left-orderable quotients, e.g. perfect ones.
   - **A natural test case**, not checked at source: `Γ * Γ` for a perfect
     torsion-free lattice `Γ` in a higher-rank simple Lie group, if one exists.
   - **Why it fits:** its quotients are finite or `Γ`, by the normal subgroup
     theorem, and such lattices are not left-orderable (Deroin–Hurtado).
