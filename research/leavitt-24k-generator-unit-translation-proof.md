---
rg: 2
id: leavitt-24k-generator-unit-translation-proof
kind: route
title: Check the nine prefix-code products and push the elementary matrices through
target: leavitt-24k-generators-as-explicit-units-of-the-ring
requires:
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
artifacts:
  - research/artifacts/leavitt-tracial-moment-relaxation-no-go-2026-09-08.md
---

## Proof

**The nine products.**  Each collapses by one application of
`t_i s_j = delta_(ij)`:

```text
r_1p_1 = t_0s_0 = 1,        r_1p_2 = t_0(s_1s_0) = 0,
r_1p_3 = t_0(s_1s_1) = 0,   r_2p_1 = (t_0t_1)s_0 = 0,
r_2p_2 = t_0(t_1s_1)s_0 = t_0s_0 = 1,
r_2p_3 = t_0(t_1s_1)s_1 = t_0s_1 = 0,
r_3p_1 = t_1(t_1s_0) = 0,
r_3p_2 = t_1(t_1s_1)s_0 = t_1s_0 = 0,
r_3p_3 = t_1(t_1s_1)s_1 = t_1s_1 = 1.
```

**The resolution of the identity.**  Using `s_0t_0 + s_1t_1 = 1` twice,

```text
sum_i p_ir_i = s_0t_0 + s_1s_0t_0t_1 + s_1s_1t_1t_1
             = s_0t_0 + s_1(s_0t_0 + s_1t_1)t_1
             = s_0t_0 + s_1t_1 = 1.
```

**`Theta` is an isomorphism.**  Multiplicativity:

```text
Theta(A)Theta(B) = sum_(i,j,k,l) p_i a_(ij) r_j p_k b_(kl) r_l
                 = sum_(i,j,l) p_i a_(ij) b_(jl) r_l = Theta(AB),
```
by `r_jp_k = delta_(jk)`.  Unitality is `Theta(I) = sum_i p_ir_i = 1`.
The map `z |-> (r_i z p_j)` is a two-sided inverse: composing one way
gives `r_i (sum_(k,l) p_k a_(kl) r_l) p_j = a_(ij)`, and the other way
gives `sum_(i,j) p_i r_i z p_j r_j = z`, again by the two displayed
identities.

**The generators.**  `b_1 = x_12(s_0) = I + s_0E_12`, so
`Theta(b_1) = sum_i p_ir_i + p_1 s_0 r_2 = 1 + p_1s_0r_2`, and likewise
for `b_2, b_3`.  The 3-cycle `c` has entries `a_21 = a_32 = a_13 = 1` and
all others zero, giving `Theta(c) = p_2r_1 + p_3r_2 + p_1r_3`.  These are
units because `Theta` is a ring isomorphism and the originals are
invertible.

**The generation statement transfers** because `Theta` restricts to a
group isomorphism `GL_3(R) -> R^x`, and the prerequisite identifies
`EL_3(R)` with `H = R^x` and proves the four elements generate it.  Orders
three and eight, and the subgroup structure, are preserved by any group
isomorphism.
