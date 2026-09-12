---
rg: 2
id: affine-seven-generator-distance-from-rational-factor
kind: route
title: Evaluate the rational Hodge factor and average the bounded translation orbit
target: affine-seven-generator-distance-estimate
requires: []
artifacts:
  - experiments/sl3-sos-radius0-certificate.npz
  - experiments/verify_affine_hodge_certificate.py
  - research/artifacts/p13-rational-certificate-audit-2026-09-08.md
  - research/artifacts/affine-seven-generator-distance-estimate-2026-09-08.md
  - research/artifacts/affine-hodge-integer-check-2026-09-08.json
---

The certificate appendix defines the six matrices, all thirteen relation
words, the Fox matrices `D,F`, and the fixed integer factor `Q`. Exact
coefficient arithmetic gives

```text
FD=0,
F*F+DD*=(1/250)I+Q*Q+R,
max(row_l1(R),column_l1(R))=11670886519714/10^16 < 1/500.
```

The Schur estimate bounds the represented residual in every Hilbert-space
representation. Testing the resulting Hodge lower bound on `Dx` gives
`A^2 >= A/500` for `A=D*D`, hence the six-generator distance bound
`sqrt(3000) max ||pi(s)x-x||`.

Every integer vector `(a,b,c)` is the sum of the primitive vectors
`(a-1,b,1)` and `(1,0,c-1)`. Integral row operations put each primitive
vector in the `SL_3(Z)` orbit of `e_1`. Projecting to the rotation-fixed
subspace and taking the least-norm point in the closed convex translation
orbit therefore gives the constant `2+5 sqrt(3000)`. Continuous functional
calculus gives the asserted C-star spectral projection.

The appendices prove each step, including the all-representations scope.
The integer verification artifact records the independent MSI replay.
No qualitative group rigidity theorem is invoked as a premise.
