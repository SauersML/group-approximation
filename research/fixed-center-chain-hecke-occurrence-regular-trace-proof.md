---
rg: 2
id: fixed-center-chain-hecke-occurrence-regular-trace-proof
kind: route
title: Apply the two affine selector traces on the nonzero regular Hecke corner
target: fixed-center-chain-hecke-occurrence-is-regularly-impossible
requires:
  - center-chain-hecke-polar-supports-are-nested-pauli-flags
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
---

The center-chain support calculation gives fixed group-algebra projections
`p_2<=p_1<=e` with canonical traces

```text
tau(e)=1/64,       tau(p_1)=1/256,       tau(p_2)=1/512.
```

Hence every proposed fixed ordinary-word occurrence row may be evaluated in
the left regular representation on a nonzero finite tracial corner.  The
claimed native typing and the exact relative Pauli-commutant gauge would put
the two selector outputs in the hypotheses of the affine trace formula with
one common gauge fraction `theta`.  Substitution of `(r,q)=(1/2,1/4)` gives
`theta=1/2`; substitution of `(r,q)=(1/4,1/8)` gives `theta=5/6`.
This contradiction proves that the proposed fixed occurrence row cannot
exist.  The calculation is internal to the canonical group trace and uses
neither Property `(T)` nor any stability theorem.
