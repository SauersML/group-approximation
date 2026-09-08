---
rg: 2
id: tensor-diagonal-and-expectation-preserve-commutant-excess
kind: route
title: Compute diagonal Fourier invariants and keep their separation under conditional expectation
target: diagonal-leavitt-models-have-external-commutant-excess
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-elementary-group-is-simple
  - leavitt-center-is-coefficient-field
artifacts:
  - research/artifacts/leavitt-diagonal-external-commutant-obstruction-2026-09-08.md
---

Block commutation with elementary roots gives `C_H(L)=K`.
Infinite simplicity implies that every finite conjugation orbit of
`L` in `H times H` is a singleton. The singleton pairs are exactly
`K times K`, so the Fourier fixed-vector computation gives
`Delta(A)' intersect M=B tensor B`. The same computation for `H`
gives `Delta(N)' intersect M=C`.

For `k!=1`, the vector `x=lambda_k tensor I` is supported outside
the diagonal subgroup of `K times K`, so `E_(Delta(B))(x)=0`.
In a finite extension `Q`, conditional expectation onto `M` sends
`Delta(N)' intersect Q` to the scalars. Since this algebra commutes
with `Delta(B)`, expectation sends their generated algebra `D_Q`
into `Delta(B)`. Hence `x` is orthogonal to `D_Q`, proving exact
distance one.

Tensor-product microstates embed `L(H times H)=N tensor N` whenever
`H` is hyperlinear. The artifact checks the frozen finite-factor
multiplicities and the factor-two word-defect bound directly.
It reproves the needed group centralizers and uses no uncommitted
internal-commutant theorem. All native word identities survive the
diagonal embedding, while the restriction to `H` has its regular
character.

The example refutes a universal external-commutant inference from
those exact identities and trace information. It makes no claim
that every embedding has this excess or that no special embedding
could support a different correction argument.
