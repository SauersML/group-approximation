---
rg: 2
id: normal-rank-one-free-products-need-cyclic-abelianization
kind: claim
title: Constraints on a free product of nontrivial groups that one element normally generates
distinct_from:
  left-orderable-free-products-have-normal-rank-above-one: that is the input theorem for two left-orderable factors; this combines it with abelianization and Kervaire--Laudenbach inputs into necessary conditions on any normal-rank-one free product, with any number of factors.
  gordon-free-products-of-three-groups-have-normal-rank-above-one: that is the open conjecture that three or more factors never give normal rank one; this lists conditions a counterexample to it must meet.
  torsion-free-free-products-have-normal-rank-above-one: that is the open two-factor torsion-free question; this narrows what a counterexample to it must look like.
---

**ESTABLISHED** by `normal-rank-one-free-product-constraints-proof` (elementary,
given the imported theorems).

**Statement.** Let `G = A_1 * ... * A_n` with `n >= 2` and every `A_i` nontrivial,
and suppose `G = <<w>>` for a single element `w`. Then:
- **(a)** `A_1^ab ⊕ ... ⊕ A_n^ab` is cyclic.
- **(b)** At most one factor admits a nontrivial left-orderable quotient.
- **(c)** Suppose some `A_j` maps onto `Z`, and put `H = *_{i≠j} A_i`. Then `H`
  is neither torsion-free nor hyperlinear, and every `A_i` with `i ≠ j` is perfect.

**Consequences.**
- **Kirby Problem 66** (`torsion-free-free-products-have-normal-rank-above-one`).
  Suppose `A` and `B` are nontrivial torsion-free groups and `A * B` has normal
  rank 1. Then:
  - `A^ab ≅ Z/m` and `B^ab ≅ Z/n` with `gcd(m,n) = 1`, where `m = 1` or `n = 1`
    is allowed;
  - at least one of `A`, `B` has no nontrivial left-orderable quotient.
- **Gordon's conjecture** (`gordon-free-products-of-three-groups-have-normal-rank-above-one`).
  A counterexample with `n >= 3` factors must meet two conditions.
  - **Abelianizations.** Either the abelianizations are finite cyclic of pairwise
    coprime orders (all factors perfect, for instance), or one factor has
    abelianization `Z`, all others are perfect, and their free product is neither
    torsion-free nor hyperlinear.
  - **Orderable quotients.** At most one factor has a nontrivial left-orderable
    quotient.
- **Where Gordon's conjecture already holds.** It holds whenever two factors map
  onto `Z`, or more generally have nontrivial left-orderable quotients. It also
  holds whenever two factors have abelianizations whose direct sum is not cyclic.
  For factors with torsion, the case left is finite, or perfect, factors.
