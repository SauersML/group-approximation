---
rg: 2
id: marked-clifford-compressor-hyperfinite-invisibility
kind: claim
title: A finite Clifford block and an abelian compressor force hyperfinite mark invisibility
distinct_from:
  literal-group-mark-invisible-to-hyperfinite-representations: that verifies the criterion for the literal group E using its eight-site block, dyadic doubling, and the SL_3(Z) action; this is the abstract marked-group theorem.
  hyperfinite-covariant-obstruction-lemma: that starts by assuming proper outerness of a nonamenable action on a represented lamp closure; this derives proper outerness from a finite Clifford trace computation, compressor conjugacy, and Haar-null fixed sets on an abelian dual.
  literal-central-mark-corona-invisible: that is an operator-norm matrix-corona theorem driven by property (T); this is a finite-injective representation theorem and uses no property (T).
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `Gamma` be a group with a central involution `w`.  Suppose it contains
a semidirect product

```text
B=N semidirect H,
```

where `N` is countable abelian and `H` is nonamenable.  Assume:

1. `Gamma` contains involutions `c_1,...,c_(2m)`, with `m>=1`, satisfying

   ```text
   c_i c_j=w c_j c_i                  (i!=j).
   ```

2. There is a set `V subset Gamma` such that conjugation by every `v in V`
   permutes the `2m` elements `c_i` by a fixed-point-free involution.
3. Every `n in N\{e}` is conjugate in `Gamma` to an element of `V`.
4. For every `h in H\{e}`, the fixed-point set of the dual action on
   `N_hat` has Haar measure zero.

Then every homomorphism from `Gamma` to the unitary group of a finite
injective von Neumann algebra kills `w`.

The criterion is entirely representation-free.  Its finite Clifford block
forces trace zero on `V`; the compressor condition propagates this to the
regular character on `N`; the dual fixed-set hypothesis makes the represented
`H`-action properly outer; and nonamenability contradicts injectivity.  No
Kazhdan property, residual finiteness, character classification, invariant-
measure rigidity, or profinite-continuity hypothesis is used.
