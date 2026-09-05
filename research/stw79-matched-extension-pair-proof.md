---
rg: 2
id: stw79-matched-extension-pair-proof
kind: route
title: Compare a split quasidiagonal extension with Park's Toeplitz rotation extension
target: stw79-same-factors-different-decomposition-rank
requires:
  - stw79-total-order-af-index-dr-dichotomy
artifacts:
  - research/artifacts/stw79-index-dichotomy-2026-09-04.md
---

On `l2(N)` let `S e_n=e_(n+1)` and `V e_n=exp(2 pi i n theta)e_n`.
The algebra `T_theta=C*(S,V)` contains `K` essentially, has quotient
`A_theta`, and has index vector `(-1,0)`: this is Park's Theorem 2 and
Proposition 5, also checked directly in the artifact. Put
`E_1=T_theta tensor U`.

Choose a faithful quasidiagonal unital representation `rho` of `A_theta`
on a separable infinite-dimensional Hilbert space and put
`E_0=(K+rho(A_theta)) tensor U`. Simplicity makes the representation
essential, and the defining extension splits, so its index is zero.
Tensoring by the CAR algebra preserves essentiality, exactness and the
identified endpoint algebras. The quotient is AT, with decomposition
rank one and K-groups `Z[1/2]^2`. Apply the prerequisite to obtain both
decomposition ranks and the nuclear-dimension bounds.

Every bounded trace on `K tensor U` vanishes, by arbitrarily many
orthogonal equivalent matrix-corner projections. Hence every tracial
state of either middle algebra factors through the same monotracial
quotient. The artifact supplies all details, including preservation of
essentiality and the proper-isometry witness in `E_1`.
