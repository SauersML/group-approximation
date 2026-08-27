---
rg: 2
id: literal-compressor-augmentation-proof
kind: route
title: Count transvection two-cycles and then inspect the restriction-ring kernel
target: literal-compressor-excludes-augmentation-regular-approximants
requires: []
---

Put `V=F_2^(8N)`.  The permutation action of `G_m=GL(V)=SL(V)` on
`V\{0}` is two-transitive, so its complement to the constants is the
irreducible augmentation representation `pi_m`.

For an involution `g`, every nonfixed orbit on `V\{0}` is a two-cycle.  The
negative eigenspace of its complex permutation matrix therefore has dimension

```text
(2^(8N)-2^dim ker(g-1))/2,                            (LCP1)
```

and deleting the constant vector does not change that dimension.  Since
`rank(A_m-1)=2^m=N/3`, the fixed-space dimensions of `alpha_m` and `beta_m`
are respectively `22N/3` and `23N/3`.  Their negative eigenspaces in
`pi_m` have different ranks.  If `P,Q` are the corresponding negative
spectral projections, then `rank(P)!=rank(Q)`, hence `||UPU^*-Q||=1` for
every unitary `U`.  Replacing the projections by the self-adjoint
involutions `1-2P` and `1-2Q` proves `(LCA2)`.

For a fixed nonidentity degree-zero element `g`, block flattening multiplies
`rank(g-1)` by `2^m`.  The normalized permutation character is, up to the
deleted constant summand,

```text
(2^dim ker(g-1)-1)/(2^(8N)-1),
```

and therefore tends to zero.  This proves the regular-character limit.

For the limitation, let `H=SL_N(2)` and `G=SL_(8N)(2)`.  Stable block
embedding injects conjugacy classes of `H` into those of `G`: rational
canonical form recovers the original class after deleting the added
one-dimensional identity blocks.  The three unipotent classes with Jordan
partitions `(8N)`, `(8N-1,1)`, and `(8N-2,2)` are not in that image.  Hence
the numbers of complex irreducible characters satisfy

```text
rank R(G) >= rank R(H)+3.
```

It follows that the integer kernel of
`Res_alpha-Res_beta:R(G)->R(H)` has rank at least three.  The trivial and
regular characters lie in the kernel: the former restricts trivially and
the latter restricts to `[G:H]` copies of the regular representation of
`H`, independently of the embedding.  Choose an integral kernel vector `x`
outside their span.  For sufficiently large `M`, every irreducible
coefficient of `M Reg_G+x` is nonnegative, so it is the character of a
genuine faithful representation, is nonregular, and has equivalent
`alpha`- and `beta`-restrictions.  Letting `M` grow makes its normalized
character arbitrarily close to the regular character.  Thus restriction
multiplicity for this one compressor edge cannot close the MF obstruction.
