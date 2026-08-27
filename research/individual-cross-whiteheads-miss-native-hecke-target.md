---
rg: 2
id: individual-cross-whiteheads-miss-native-hecke-target
kind: claim
title: An individual cross-branch Whitehead misses both native row-one Hecke targets
artifacts:
  - research/individual-cross-whitehead-typing-proof.md
distinct_from:
  cross-branch-partial-whiteheads-have-finite-wreath-gauge-model: that types the product of the two cross-branch factors through the aggregate branch flip; this tests each factor before multiplication and compares it with the literal native Whitehead and Singer targets.
  eight-external-returns-have-no-whitehead-gauge-lock: that exhausts constant-root normalizers against the native Whiteheads; these are nonconstant opposite-root words built from the two cross matrix units.
  one-asymmetric-prefix-cannot-be-signed-hecke-return: that detects one nonconstant root coefficient; this computes a three-root opposite-Whitehead occurrence and its relative word with the native `J_1`.
---

**ESTABLISHED INDIVIDUAL-TYPING FENCE.**  Keep

```text
p=s_0t_1,       r=s_1t_0,       q_i=s_it_i,
K_0=x_78(p)x_87(r)x_78(p),
K_1=x_78(r)x_87(p)x_78(r).                         (IKT1)
```

Let `Q=e_(L_0,lambda_0)` be the signed Hecke cut and use the literal
generator `h=x_28(1)` of `L_0`.  The two-by-two blocks from the
cross-branch calculation give

```text
K_0 h K_0=x_27(r)x_28(q_0),
K_1 h K_1=x_27(p)x_28(q_1).                         (IKT2)
```

Both right sides have nonconstant Leavitt entries.  Since every matrix in
the constant group `L_0` has all entries in the embedded `F_2`, neither
right side belongs to `L_0`.  Thus neither individual `K_i` normalizes the
signed Hecke pair; in particular it is not an endomorphism of the carrier
`Q`.

This failure is not repaired by typing `K_i` against the first native
Whitehead target.  On ordered coordinates `(7,8)`, write

```text
J_1=[[1-q_0,y_1],[x_1,1-e_00]],
x_1=s_00t_0,       y_1=s_0t_00,       e_00=s_00t_00. (IKT3)
```

Directly applying this block to `(IKT2)` gives

```text
(J_1K_0)h(J_1K_0)^(-1)
  =x_27(x_1)x_28(s_1t_00+q_0+e_00),
(J_1K_1)h(J_1K_1)^(-1)
  =x_27(p)x_28(q_1).                                (IKT4)
```

Again these elements are not in `L_0`.  Hence

```text
J_1^(-1)K_i notin Norm(L_0,lambda_0),                (IKT5)
```

so `K_iQK_i^(-1)` is neither `Q` nor `J_1QJ_1^(-1)`.  Since
`t_1=J_1v_1` with `v_1` in the signed normalizer, the same statement holds
with the Singer target:

```text
t_1^(-1)K_i notin Norm(L_0,lambda_0).                 (IKT6)
```

There is one short literal native relation, but it is a moving-cut relation,
not the missing same-carrier lock.  For the constant root-position Weyl
`w=w_78(1)` and the aggregate flip `T=K_0K_1`, block swapping gives

```text
wK_0w=K_1,       wK_1w=K_0,       [w,T]=1.           (IKT7)
```

Even if one records the corresponding reservoir equation, it does not kill
the native order-three holonomy.  The complete local gauge table consisting
of involutions `D,E,k_0,k_1`,

```text
Dk_0D=k_1,       k_0k_1=t,       [D,t]=1,
F=DED,           D=EFE,                                  (IKT8)
```

has the exact finite `S_4` model

```text
D=(1 2),         E=(2 3),         F=(1 3),
k_0=(1 3)(2 4),  k_1=(1 4)(2 3),  t=(1 2)(3 4).       (IKT9)
```

Here `DE` is a three-cycle.  Thus the first individual/native Weyl square
does not force the two gauges to commute or cancel.  Equations `(IKT2)` and
`(IKT4)--(IKT6)` also show why arbitrary `J_1` or Singer naturality cannot
be read as such a square: its two paths do not have the same Hecke target.

This is a scoped finite model of the new individual/Weyl gauge equations,
not a finite representation of EL20 or a replacement for the established
aggregate wreath model.  A positive ESB word must add another nonconstant
return which brings one `K_i` cut back to `Q` or to the native `J_1` target;
merely juxtaposing `K_i` with `J_1`, `t_1`, or `w` does not type a common
carrier.

No Property T, Kazhdan input, trace hypothesis, local computation,
literature theorem, or Lean compilation is used.

DERIVATION
individual-cross-whitehead-typing-proof
