---
rg: 2
id: coefficient-central-affine-leavitt-envelope-is-morita-trivial
kind: claim
title: Centralizing the affine head reduces the active envelope to two matrix-amplified ordinary Leavitt algebras
distinct_from:
  affine-active-head-central-leavitt-envelope: that proves the stronger quotient is faithful and retains the active idempotent; this identifies its complete algebra structure and shows that the affine coupling has disappeared.
  affine-active-doubling-is-elementary-matrix-conjugacy: that exploits coefficient centrality to write the branch as an elementary conjugator; this explains why that conjugator is the standard Leavitt equivalence in Morita-amplified coordinates.
  affine-sign-twist-swaps-active-blocks-but-is-stationary: that retains a nontrivial affine action swapping the two active blocks; the coefficient-central quotient makes the Leavitt family trivial on both blocks separately.
---

Let `L_2(k)` be the ordinary binary Leavitt algebra and let
`R=L_A^c(S)`. Then

```text
R ~= (1-A)S times (AS tensor_k L_2(k)).                    (CMT1)
```

Indeed, send `a in S` to

```text
((1-A)a, Aa tensor 1)
```

and send each relative `s_i,t_i` to the corresponding Leavitt generator in
the second factor. This defines a homomorphism from `(ACL1)`. Conversely,
the coefficient inclusion and the multiplication map

```text
a tensor word |-> a word
```

define the inverse because all four branch generators commute with `AS` and
are annihilated by `1-A`.

Using the affine Wedderburn calculation

```text
AS ~= M_3(k) direct_sum M_3(k),
```

the active factor becomes

```text
AS tensor L_2(k)
  ~= M_3(L_2(k)) direct_sum M_3(L_2(k)).                   (CMT2)
```

Thus the coefficient-central construction is a faithful exact model and a
useful source of the elementary conjugator, but it adds no genuinely affine
nonlinearity to the active Leavitt--Steinberg problem. Any HS collapse proof
using only this quotient would already solve the ordinary matrix-amplified
`L_2(k)` Steinberg problem.

Consequently the live affine decoder must either retain the original free
relative envelope, or impose a nontrivial covariant action of the finite head
on the branch generators. Full coefficient centrality is a diagnostic
quotient, not a shortcut around the root-to-coefficient obstruction.
