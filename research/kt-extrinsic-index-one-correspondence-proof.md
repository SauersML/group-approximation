---
rg: 2
id: kt-extrinsic-index-one-correspondence-proof
kind: route
title: Generate the bimodule from the seam unitary and use its zero AFP expectation
target: kt-extrinsic-corrector-is-an-orthogonal-index-one-correspondence
requires:
  - kt-extrinsic-seam-correctors-are-orthogonal-to-the-afp-paste
  - kt-c-normalization-seam-is-a-relative-commutant-cocycle
---

The equations `zr=rz` for `r in R` and
`zv_gamma=rho_gamma z` generate `(KBC2)` by strong-operator continuity.
Since `z` is unitary, right multiplication by `z^*` identifies `H_z` with
the standard left module `L^2(B_rho)`, while left multiplication by `z^*`
identifies it with the standard right module `L^2(B_v)`.  Both dimensions
are therefore one and the supports are full.  By
`kt-extrinsic-seam-correctors-are-orthogonal-to-the-afp-paste`, `E_M(z)=0`.
For `a,b in M`, bimodularity gives

```text
E_M(a z b)=a E_M(z)b=0,
```

so the generated correspondence is orthogonal to `L^2(M)`.  The converse
is immediate from the defining equations and unitarity of the cyclic
vector.
