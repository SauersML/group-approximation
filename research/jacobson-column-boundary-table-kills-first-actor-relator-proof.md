---
rg: 2
id: jacobson-column-boundary-table-kills-first-actor-relator-proof
kind: route
title: Compute the finite boundary table and factor the affine corona models through the first actor relation
target: jacobson-column-first-actor-quotient-retains-full-column
requires:
  - jacobson-whole-column-normalizer-has-marked-lef-models
artifacts:
  - research/artifacts/jacobson-column-models-satisfy-first-actor-relation-2026-09-08.md
---

Use `W_n=A_n+F(A_n)` with the explicit complement spanned by
`x_(n,j)` and `F x_(0,n-1)`. Constants act trivially on the complement.
For `U=I+X`, `V=I+Y`, and `B=FYF`, the complete boundary table gives
`XB=0` and `X^2=B^2=0`. Hence `[U,FVF]=I+BX` has square identity
in every size, including `n=2`.

The literal actor relation acts trivially on the full additive column,
so quotienting by it preserves the column. Omit the independent actor
separating factors from the cover construction. The affine models then
descend through the new relation, and their eventual exact covariance
defines a norm-corona homomorphism retaining every nonzero translation.
Exact finite-dimensional collapse is inherited from the cover.

For the next literal relation, set `a=h(uvu)`, `r_j=a^j r a^(-j)`
and `c_2=[u,a^2 u a^(-2)]`. Relabeling the two unilateral rows
as one bilateral row gives the exact identity
`c_2=[r_1,r_(-1)][r_2,r_0]`. Its comparison word swaps two
specified points of every finite window for `n>=5`, proving norm
defect exactly `2` and showing that these models still do not descend
to the literal actor group.
