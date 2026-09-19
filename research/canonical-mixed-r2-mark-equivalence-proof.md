---
rg: 2
id: canonical-mixed-r2-mark-equivalence-proof
kind: route
title: Conjugate the fixed mixed three-cycle to the Thompson mark
target: canonical-mixed-r2-is-the-thompson-mark-obstruction
requires:
  - hs-dehn-modulus-bounded-by-dehn-function
  - mixed-r2-cell-couples-shared-s5-extension-multiplicities
  - shared-s5-selector-face-has-multiplicity-rotation-gauge
  - shared-s5-gauge-is-invisible-to-all-r4-r5-cells
---

The supports of `t_j=(j q)` and `s_i=(i p)` are disjoint.  Hence the fixed
permutation represented by `(CMO1)` is

```text
m=s_i r=(i p)(p q),
```

a nontrivial three-cycle.  Every two three-cycles of finite prefix cylinders
are conjugate in `V` after passing to a common finite prefix partition.
Choose once and for all a Bleak--Quick word `g` and an orientation
`epsilon in {1,-1}` giving `(CMO2)`.

The fixed word

```text
z=m^(-1) g^(-1)b^epsilon g
```

is trivial in `V`.  Choose one van Kampen diagram for `z` and call its area
`A`.  The HS--Dehn area estimate gives

```text
||m(U)-g(U)^*b(U)^epsilon g(U)||_2 <= A delta.
```

Unitary conjugation and inversion preserve distance to the identity, so the
reverse triangle inequality proves `(CMO3)`.  Right multiplication by
`r(U)^*` proves `(CMO4)`.

For corrected occurrences, telescope

```text
||Y^*XY-t_j(U)^*s_i(U)t_j(U)||_2
 <= 2||Y-t_j(U)||_2+||X-s_i(U)||_2
```

and then include `||R-r(U)||_2`; this proves `(CMO5)`.

For the locality assertion, use the exact rotation in
`shared-s5-selector-face-has-multiplicity-rotation-gauge`.  Both private
`S_6` multiplication tables and their common `S_5` restriction are exact.
By `shared-s5-gauge-is-invisible-to-all-r4-r5-cells`, every label-valid
disjoint-support cell, including a cross-chart one, is exact as well.  But
`mixed-r2-cell-couples-shared-s5-extension-multiplicities`, equation `(MRC5)`,
says the mixed R2 defect is precisely the positive missing-arm mismatch.
Therefore no estimate whose right-hand side uses only those finite-chart,
common-face, private-R2, and R4/R5 defects can control the mixed residual.
