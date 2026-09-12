---
rg: 2
id: leavitt-small-anchors-do-not-force-the-native-p1-square
kind: claim
title: Four short Leavitt packet rows admit a regular-profile model with a nontrivial p1 square
distinct_from:
  leavitt-seven-cell-thompson-completion-requires-moved-pairs: That obstructs specified Thompson completions in V; this gives an exact finite countermodel to deriving the native p1 square from the two anchors together with B cubed and AB to the fourth power.
  leavitt-has-an-explicit-finite-c-killing-certificate: That excludes exact finite-dimensional models of the full Thompson packet retaining c; the stronger model here satisfies its two anchors and two further short rows but explicitly fails rho5.
artifacts:
  - research/artifacts/leavitt-small-anchor-p1-square-countermodel-2026-09-08.md
---

In `P=C_3*C_2^3`, let `d,A,p_1,B` be the actual shared words
of the current native Thompson compiler. Then

```text
p_1^2 does not belong to <<d^2,(Ac)^2,B^3,(AB)^4>> in P.
```

An explicit permutation model on seven letters satisfies all four
displayed rows and makes `p_1` an element of order three. Tensoring
the six-dimensional standard representation with the regular
representation of `C_2^3` gives a dimension-48 unitary model with
the required regular profiles of both marked finite factors. In it,

```text
||d^2-I||_2=||(AC)^2-I||_2=||B^3-I||_2=||(AB)^4-I||_2=0,
||p_1^2-I||_2=||rho_5-I||_2=sqrt(2).
```

The norms are normalized Hilbert--Schmidt norms. Direct sums give
the same defects in every dimension `48r`, hence at every even
value `k=2r` of the frozen dimension `24k`.

For comparison, a simpler fixed-cell transposition already makes
the two anchor defects zero and the `p_1^2` defect one; its `B^3`
defect is `sqrt(5/3)`. The stronger example shows that adjoining
`B^3` and `(AB)^4` does not restore the implication.

The explicit failure of `rho_5` keeps the stronger example outside
`T_8`. No independence result for `p_1^2` from `T_8` is asserted.
There can be no estimate forcing that square defect to zero using
only the four displayed row defects and exact regular marked factors.
This is a written exact proof, not newly Lean-verified.

DERIVATION
seven-point-regular-padding-refutes-short-row-derivability
