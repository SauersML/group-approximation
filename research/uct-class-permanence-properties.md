---
rg: 2
id: uct-class-permanence-properties
kind: claim
title: The separable UCT class is KK-invariant and closed under semisplit extensions, nuclear inductive limits and UCT tensor factors
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (literature).**  For separable C\*-algebras:

1. `A` satisfies the UCT if and only if `A` is KK-equivalent to a commutative
   C\*-algebra (Rosenberg--Schochet, Duke Math. J. 55 (1987); Dadarlat,
   *Some remarks on the universal coefficient theorem in KK-theory* (2003),
   Proposition 2.1(1)).  In particular the class is invariant under
   KK-equivalence.
2. If `0 → J → A → B → 0` is a semisplit exact sequence and two of `J`, `A`,
   `B` satisfy the UCT, then so does the third (Dadarlat, Proposition 2.1(2)).
3. An inductive limit of UCT algebras whose limit is nuclear satisfies the UCT
   (Dadarlat, Proposition 2.1(3)).
4. Tensor products, direct sums, suspensions and stabilizations of UCT
   algebras satisfy the UCT, and so do crossed products of UCT algebras by `Z`
   or `R` (Brown--Browne--Willett--Wu, *The UCT problem for nuclear
   C\*-algebras* (2020), Section 3.1, citing Rosenberg--Schochet
   Propositions 2.3, 2.6 and 2.7).

These are the permanence facts used by `coprime-uhf-stabilizations-detect-uct`.
