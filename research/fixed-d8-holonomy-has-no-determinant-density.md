---
rg: 2
id: fixed-d8-holonomy-has-no-determinant-density
kind: claim
title: A fixed D8 projective holonomy cannot amplify determinant or index parity to HS density
distinct_from:
  projective-holonomy-rank-forces-exponential-multiplicity: that computes the exact divisor forced by an arbitrary binary cocycle rank; this gives the explicit normalized-HS repair and records that tensoring with the native positive-density D8 carrier does not improve it.
  additive-index-instability: that kills determinant parity by tensor amplification; this treats a fixed projective packet on every D8 spin copy and shows directly that the external multiplicity remainder is still sublinear.
  single-triangle-trace-cyclic-return-cell: that asks for a proper-corner loss proportional to the whole selected carrier; this rules out replacing that loss by any fixed number of projective/determinant orientation checks.
---

Fix a finite system `R` of unitary word relations which has an exact
`q`-dimensional solution.  For every `m`, write

```text
m=q l+s,                    0<=s<q.                    (FDH1)
```

Put `l` copies of the exact solution on the first `ql` coordinates and put
arbitrary unitaries on the remaining `s` coordinates.  For every relator
`r in R`,

```text
||r(U)-I||_(2,m) <= 2 sqrt(s/m) < 2 sqrt(q/m).         (FDH2)
```

Thus every fixed projective commutator, determinant parity, or finite
Clifford-holonomy obstruction has vanishing normalized-HS cost as external
multiplicity grows.  If the packet is tensored with the native two-dimensional
D8 spin carrier `T`, normalized HS norm factorizes:

```text
||I_T tensor (r(U)-I)||_(2,2m)=||r(U)-I||_(2,m).       (FDH3)
```

Meanwhile the selected D8 projection is `I_T tensor I_m` on that sector and
retains full conditional density.  Hence the positive-density D8 cut does
not turn the `O(1)` bad multiplicity coordinates in `(FDH2)` into a positive
density of bad coordinates.

For one anticommuting pair, `q=2`: use Pauli blocks on `m-1` coordinates and
one scalar coordinate when `m` is odd.  A fixed finite number of independent
return orientations merely replaces `q=2` by one fixed Clifford dimension
`q=2^r`; `(FDH2)` still tends to zero.

Consequently a determinant/index attack on the native triangle can work only
if it does one of the following:

1. activates cocycle rank growing with the current multiplicity;
2. produces a bounded-block obstruction independently on a linear number of
   multiplicity coordinates; or
3. proves the genuine proper-corner comparison of `(STR1)`, whose missing
   rank is proportional to the whole carrier rather than to one remainder
   block.

The first two alternatives require a growing multiplicity-coordinate
sampler.  The fixed D8 packet and any fixed pair of field/orientation
matchings act only on a bounded packet factor and cannot supply that sampler.
