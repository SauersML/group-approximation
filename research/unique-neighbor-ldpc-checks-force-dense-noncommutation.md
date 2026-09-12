---
rg: 2
id: unique-neighbor-ldpc-checks-force-dense-noncommutation
kind: claim
title: Unique-neighbor LDPC checks force exact noncommutation to have quadratic support
distinct_from:
  sparse-clifford-cycles-refute-average-commutator-rounding: that gives a sparse cycle with no parity checks; this proves that unique-neighbor parity checks exclude precisely that support pattern.
  disjoint-private-pairs-expand-the-full-exterior-square: that detects central class-two commutation signs by sampled wedges; this applies to arbitrary exact reflections and uses only the support of nonidentity commutators.
  positive-rate-tanner-tests-have-contextual-models: that constructs local contextual representations; this identifies an additional stopping-set restriction imposed by a unique-neighbor Tanner graph.
---

Let `H` be a binary parity-check system on `L` coordinates with stopping
distance at least `sigma L`: every nonempty set of fewer than `sigma L`
coordinates has a check meeting it in exactly one coordinate.  Let
`Q_1,...,Q_L` be reflections in an arbitrary tracial von Neumann algebra.
Assume that, in every check `T`, the reflections `(Q_i)_(i in T)` commute and

```text
prod_(i in T) Q_i=1.                                      (UND1)
```

For fixed `j`, put

```text
S_j={i: [Q_i,Q_j] != 0}.
```

Then `S_j` is a Tanner stopping set.  Hence it is empty or
`|S_j|>=sigma L`.  By symmetry, if any pair fails to commute, at least

```text
sigma^2 L^2                                               (UND2)
```

ordered pairs fail to commute.

Indeed, if a check `T` met `S_j` only in `i`, then `(UND1)` would express
`Q_i` as the product of the other, pairwise commuting check reflections.
Every one of those other factors commutes with `Q_j`, forcing `Q_i` to
commute with `Q_j`, a contradiction.  If `S_j` is nonempty, it contains at
least `sigma L` indices `i`; symmetry makes every corresponding `S_i`
nonempty and therefore of size at least `sigma L`, proving `(UND2)`.

This exactly excludes the support pattern in
`sparse-clifford-cycles-refute-average-commutator-rounding` once the cycle
tuple is required to satisfy the LDPC parity contexts.  It is deliberately
only a zero-defect/support theorem.  The condition `[Q_i,Q_j] != 0` has no
uniform normalized-HS scale, so `(UND2)` alone does not imply approximate
rounding.  A quantitative proof needs an operator-valued local-testability
or cosystolic estimate, not merely classical distance or stopping distance.
