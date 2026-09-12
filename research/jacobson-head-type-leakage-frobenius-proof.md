---
rg: 2
id: jacobson-head-type-leakage-frobenius-proof
kind: route
title: Upgrade the two-chirality elimination to Frobenius norm and charge the spectral-sign compression error
target: jacobson-small-braid-defect-forces-head-type-leakage
requires:
  - del2-three-dimensional-head-braid-gap
  - binary-jacobson-gl3-k-branching-has-regular-counterprofile
artifacts:
  - research/artifacts/jacobson-all-head-braid-multiplicity-and-leakage-2026-09-08.md
---

The exact block calculation in the first prerequisite gives, on three
copies of a multiplicity space of dimension `m/3`,

```text
D_0+7J D_0 J=-6R_22-18R_33,          D_0=d+2e,
```

with `d,e,J` unitary. Applying the Hilbert--Schmidt reverse triangle
inequality and Cauchy--Schwarz to the two diagonal blocks yields

```text
||R||_F>=sqrt(m/30).
```

For a general head mixture, compress `H` to the three-dimensional head
subspace `P` and take its spectral sign `H_0`. It still commutes with
the overlap. With `E=(I-P)HP`, the identity
`P-(PHP)^2=E*E` and the scalar inequality
`(sign(t)-t)^2<=1-t^2` show

```text
||HP-H_0||_F<=sqrt(2)||E||_F.
```

Since `B` preserves `P`, telescoping the three factors of its braid
charges at most three copies of this error. The restricted full braid
residual has norm at most `delta sqrt(m)`, giving `(HTL1)`.

The second prerequisite gives the dimension of the sign and standard
overlap types in heads `6,7,8`. No trivial overlap type can receive
`E`; this gives the target-space bound used for `(HTL3)`.
The attached proof tracks every constant and uses no numerical search.
