---
rg: 2
id: native-j1-extension-gives-gl5-but-only-second-whitehead-gram
kind: claim
title: Adding J1 gives a literal GL5 block but forces only the second native Whitehead Gram
artifacts:
  - research/native-j1-gl5-source-stabilizer-proof.md
distinct_from:
  endpoint-order-five-actor-has-half-gram: that obtains GL4 and a one-third endpoint Gram from W and the second native head; this adjoins the first native Whitehead and computes a stabilizer which acts on both native Whitehead supports.
  native-whitehead-corner-collapses-hecke-flags: that computes the exact regular-profile supports q1 and q2 of the compressed native Whiteheads; this supplies a profile-uniform lower bound for q2 but fences the analogous q1 inference.
---

**ESTABLISHED LITERAL BLOCK AND ONE-SIDED NATIVE GRAM.**  On the five
equivalent projective summands

```text
u_0=q@5, u_1=e_1@7, u_2=e_2@8, u_3=e_3@9, u_4=e_3@2
```

put

```text
D_5=qE_55+e_1E_77+e_2E_88+e_3E_99+e_3E_22.           (GFI1)
```

The group `<W,M>` is the literal `GL_4(F_2)` on
`<u_0,u_2,u_3,u_4>` and fixes `u_1`.  The native `J_1` swaps `u_1,u_2`.
Consequently

```text
<W,M,J_1>|_(D_5)=GL_5(F_2),                           (GFI2)
```

faithfully, and every actor is the identity on `1-D_5`.

Let `K_2=<K_1,s>` and `p_2=e_(K_2,lambda_2)` as before.  The subgroup

```text
H_2=diag(I_3,GL_2(F_2)) <= GL_5(F_2)                  (GFI3)
```

fixes signed `K_2` pointwise and acts as the full `GL_2(F_2)` on

```text
<t,s'>=<x_69(a_3),x_62(a_3)>~=C_2^2.
```

The exact second native Whitehead support is

```text
q_2=p_2(J_2p_2J_2)p_2=p_2 1_(t=+1).                  (GFI4)
```

Therefore, for some multiplicities `n_0,n_1` in every finite-dimensional
representation of this packet,

```text
rank(p_2)=n_0+3n_1,             rank(q_2)=n_0+n_1,
rank(q_2)>=(1/3)rank(p_2).                            (GFI5)
```

This is a representation-universal positive Gram for the **actual** `J_2`
compression.

The first support has a different type:

```text
q_1=p_2(J_1p_2J_1)p_2=p_2 1_(r=+1),
r=x_58(a_2).                                          (GFI6)
```

Every element of `H_2` fixes `r`; hence `(GFI3)` gives no positive lower
bound for `q_1`.  The local stabilizer interface permits `r=-1` on a
nonzero `p_2` block.  This is only a scoped stabilizer profile, not a
countermodel to every moving `GL_5` relation, but it prevents promotion of
`(GFI5)` to a two-row theorem.

Thus adding `J_1` gives a real `GL_5` strengthening and the native `J_2`
bound `(GFI5)`, but not the first native Gram.  No claim about the complete
signed Hecke source `Q` follows from this five-summand calculation: its four
extra roots carry coefficient incidences not represented by the bare
projective block.  That separate interface remains governed by
`endpoint-order-five-return-leaves-full-hecke-fine-sign-free`.

No Property `(T)`, enumeration of `GL_5(F_2)`, canonical trace, local
computation, or Lean compilation is used.

DERIVATION
native-j1-gl5-source-stabilizer-proof
