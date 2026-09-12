---
rg: 2
id: full-prefix-three-state-model-proof
kind: route
title: Conjugate the root cell through the three nonzero two-bit characters
target: full-prefix-range-cells-have-three-state-model
requires:
  - one-arm-range-sum-whitehead-has-marked-model
---

Use the depth-one model on

```text
H=C^3 tensor C^2 tensor C^2
```

and denote its three signs by

```text
S_a=diag( 1,-1,-1),
S_b=diag(-1,-1, 1),
S_c=diag(-1, 1,-1).                                   (1)
```

They are the three nonzero characters of `F_2^2`; in particular the product
of any two distinct signs is the third.  Let

```text
w_0=(0 2),                    w_1=(0 1)                 (2)
```

on the `C^3` factor.  Then `w_0S_aw_0^(-1)=S_b` and
`w_1S_aw_1^(-1)=S_c`, and `w_0,w_1` generate the full permutation group of
`{S_a,S_b,S_c}`.

For a binary word `u=i_1...i_k`, choose its address product recursively by

```text
g_empty=1,
g_(ui)=g_u w_i.                                        (3)
```

Define the whole cell at `u` to be `g_u` times the fixed depth-one cell
times `g_u^(-1)`.  Thus

```text
J_u=g_uS_ag_u^(-1),
C_(u,i)=g_uS_(b or c)g_u^(-1),
W_(u,i)=g_uw_ig_u^(-1).                               (4)
```

The two child signs in `(4)` are the two signs distinct from `J_u`, so their
product is `J_u`.  Also

```text
J_(ui)=g_uw_iS_aw_i^(-1)g_u^(-1)=C_(u,i),             (5)
```

which proves coherent parent/child gluing.

The character permutations act trivially on the two Pauli factors.  Hence
the global authenticated arms remain fixed, while each complementary arm is
the controlled Pauli `Z` on the negative projection of the current sign.
Conjugating the depth-one equations proves `(FPT1)--(FPT2)` at every vertex.
Because `(3)` takes values in the six-element group `S_3`, arbitrarily many
address words collide, but every occurrence chart and every comparison
inside one local cell remains a literal conjugate of the same fixed table.

For the reverse-range zero product, use composable-root role copies of
`C_(u,0),C_(u,1)` acting diagonally on the character factor.  Their
commutator is one, so the `e_(u,0)e_(u,1)=0` output root is exact and this
choice is preserved by every `g_u`.  More concretely, if

```text
P_u=(1-J_u)/2,             P_(u,i)=(1-C_(u,i))/2,
```

then direct inspection of the three diagonal entries gives

```text
P_uP_(u,0)P_(u,1)=0,
P_uP_(u,0)+P_uP_(u,1)=P_u,                             (6)
```

while each `P_(u,i)` has one further rank-one character wing in `1-P_u`.
This is why the crossed-zero row is exact on the parent atom without making
either Whitehead a same-atom inverse transport.

The construction is independent of `N` and has `dim(H)=12`.  Taking any
`N>=4` already gives depth greater than `log_2(12)`, with zero defect in all
listed prototype rows.  Therefore no dimension-independent `(BAC1)` gap can
follow from this local full-tree menu.
