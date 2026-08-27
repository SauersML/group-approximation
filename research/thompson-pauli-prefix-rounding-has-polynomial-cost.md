---
rg: 2
id: thompson-pauli-prefix-rounding-has-polynomial-cost
kind: claim
title: Thompson-addressed Pauli prefixes round one new cell with polynomial depth cost
distinct_from:
  uniform-relative-clifford-tape-cell: that asks for a depth-independent local modulus; this proves the weaker polynomial-depth modulus actually sufficient for the Fanizza contraction series.
---

In `thompson-clifford-central-product-tape`, put

```text
x_i=0^i 1 0^infinity,
E_n=<J,p_(x_i),q_(x_i):0<=i<n>.
```

Conditional on an exact `J=-1` realization of `E_n`, any proposed new pair
`P,Q` at `x_n` whose addressed cross-commutators and one-cell Pauli table have
root-mean-square defect `delta_n` can be flexibly corrected, relative to the
old prefix, to

```text
P=I_(2^n) tensor P_0,       Q=I_(2^n) tensor Q_0
```

with normalized-HS loss `O(sqrt(n+1) delta_n)` and discarded density
`O((n+1)delta_n^2)`.  The constants are independent of matrix rank and
external multiplicity.

For a tuple of total defining-relator energy `E`, the Thompson address words
and the two orbit-types of lamp commutators give

```text
delta_n <= C(n+1)^c sqrt(E),                                  (TPR1)
```

for fixed `C,c`.  Hence the complete one-cell cost is still
`C'(n+1)^(c+1) sqrt(E)`.  Such a polynomial loss is summable in
`contractive-computation-ladder`; a constant per-level expander gap is not
needed for the backward ledger.
