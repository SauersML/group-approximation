---
rg: 2
id: marked-clifford-compressor-hyperfinite-invisibility
kind: claim
title: A trace-singular signed Clifford action and an abelian compressor force hyperfinite mark invisibility
distinct_from:
  finite-packet-compressor-hyperfinite-invisibility: that replaces the Clifford block by an arbitrary finite subgroup and permits several negative irreducible blocks, charging only fixed blocks to traceless normalizer implementers; this supplies a concrete signed-cycle test for its single spin block.
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

2. There is a set `V subset Gamma` such that for every `v in V` there are a
   permutation `pi_v in Sym(2m)` and exponents `delta_i(v) in {0,1}` with

   ```text
   v c_i v^(-1)=w^(delta_i(v)) c_(pi_v(i)).             (MCC0)
   ```

   For at least one cycle `D` of `pi_v`,

   ```text
   sum_(i in D) delta_i(v) = |D| mod 2.                 (MCC0')
   ```
3. Every `n in N\{e}` is conjugate in `Gamma` to an element of `V`.
4. For every `h in H\{e}`, the fixed-point set of the dual action on
   `N_hat` has Haar measure zero.

Then every homomorphism from `Gamma` to the unitary group of a finite
injective von Neumann algebra kills `w`.

The criterion is entirely representation-free.  Condition `(MCC0')` says
that the signed permutation has a cycle whose sign-product is
`(-1)^(length)`; the exact Clifford cycle formula therefore forces trace zero
on `V`.  The compressor condition propagates this to the regular character
on `N`; the dual fixed-set hypothesis makes the represented `H`-action
properly outer; and nonamenability contradicts injectivity.  No Kazhdan
property, residual finiteness, character classification, invariant-measure
rigidity, or profinite-continuity hypothesis is used.

This strictly contains the previous fixed-point-free-involution criterion:
an unsigned transposition satisfies `(MCC0')`, but so does any unsigned even
cycle, any negatively signed odd cycle, or any signed permutation containing
one such cycle, with arbitrary remaining cycles and fixed points.
