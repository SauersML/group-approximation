---
rg: 2
id: finite-morita-nonlinear-support-no-go-proof
kind: route
title: Induce every compatible selector character into the marked finite-group sector
target: finite-morita-toricization-cannot-encode-nonaffine-support
requires: []
---

Assume a full corner of a matrix amplification of `p_- C*(F)`, where
`p_-=(1-J)/2`, is Morita equivalent to `C^R` and carries each coordinate
function to `p_-z_i`.  Morita equivalence, amplification, and passage to a
full corner preserve the centre.  Hence every `p_-z_i` is central and acts
as a scalar on every irreducible `F`-representation in the `J=-1` sector.
Those joint scalars are exactly the points of `R`.

Put `A=<J,z_1,...,z_m>`.  For every character `chi` of `A` with
`chi(J)=-1`, the nonzero representation `Ind_A^F chi` lies in the marked
sector.  An irreducible summand contains `chi` upon restriction to `A`;
centrality of the `z_i` on that summand forces its joint scalar pattern to
be `(chi(z_1),...,chi(z_m))`.  Thus all compatible characters occur in
`R`, while every point of `R` is one such character.  The slice

```text
{chi in dual(A) : chi(J)=-1}
```

is affine over `F_2`, and restriction to the `z_i` coordinates preserves
affineness.  Therefore `R` must be affine, excluding every genuinely
nonaffine BCS answer support.
