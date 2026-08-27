---
rg: 2
id: binary-leavitt-heisenberg-central-self-copy-proof
kind: route
title: Apply the Leavitt prefix identities coordinatewise in the Heisenberg law
target: binary-leavitt-heisenberg-is-orthogonal-central-self-copy
requires:
  - iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
---

The central cross term in the product of two branch-`i` elements is

```text
(a t_i)(s_i b')=a(t_i s_i)b'=ab',
```

so `alpha_i` preserves `(HSC1)`.  If `a t_i=0`, multiply on the right by
`s_i`; if `s_i b=0`, multiply on the left by `t_i`.  This proves injectivity.

For `i!=j`, both cross terms in the group commutator vanish by
`t_i s_j=t_j s_i=0`, so the two images commute.  Equality of a branch-zero
and branch-one element forces both first coordinates and both second
coordinates to vanish after multiplying by the appropriate `s_i` and
`t_i`; their intersection is exactly `Z_0`.

Completeness gives

```text
a=(a s_0)t_0+(a s_1)t_1,
b=s_0(t_0 b)+s_1(t_1 b).
```

The commuting branch products therefore realize every `(a,b,c)`.  The
depth-`n` statement follows from the prefix identities
`t_u s_v=delta_uv` and `sum_|u|=n s_u t_u=1`.

For local finiteness over `F_q`, start with finitely many triples.  Let `A`
and `B` be the finite-dimensional `F_q`-spans of their first and second
coordinates, and let `C` be the span of their third coordinates together
with the image of `A tensor B -> R`.  The product and inverse laws keep the
generated subgroup inside the finite set `A x B x C`.

