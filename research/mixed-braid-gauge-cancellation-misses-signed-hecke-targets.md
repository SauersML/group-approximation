---
rg: 2
id: mixed-braid-gauge-cancellation-misses-signed-hecke-targets
kind: claim
title: Cancelling the mixed-braid spectator misses both signed Hecke targets
invalidates:
  - mixed-braid-relative-word-supplies-esb-bridge
artifacts:
  - research/mixed-braid-relative-target-proof.md
distinct_from:
  mixed-completeness-braid-retains-s3-square-gauge: that gives a scoped finite gauge for the aggregate braid table; this restores the actual signed Hecke target test and computes the direct relative comparison word.
  first-cross-whitehead-has-no-alternative-low-depth-return: that appends one root or one same-pair partial Whitehead directly to `K_0`; this compares `K_0` with the mixed three-coordinate completeness braid.
---

**ESTABLISHED MIXED-BRAID TARGET FENCE.**  On coordinates `(7,8,9)`, use
the notation of `mixed-completeness-braid-retains-s3-square-gauge`:

```text
U=x_78(p),       V=x_87(r),
U'=x_79(1),      V'=x_97(q_1),
A=UU',           B=VV',
G=ABA,           K=UVU.                               (MBT1)
```

The relative word which removes the displayed channel-nine factor is

```text
L=GK^(-1)=GK.
```

Direct multiplication over the binary Leavitt algebra gives

```text
L = [[q_0,0,1],
     [0,  1,r],
     [q_1,0,q_0]]                                    (MBT2)
```

in the ordered basis `(7,8,9)`.  In particular `L^2=1`.  Let
`Q=e_(L_0,lambda_0)` be the signed Hecke projection.  Since
`h=x_28(1)` belongs to `L_0`, the eighth row of `(MBT2)` gives

```text
LhL^(-1)=x_28(1)x_29(r).                              (MBT3)
```

The coefficient `r=s_1t_0` is a nonconstant reduced Leavitt matrix unit,
whereas every element of the finite signed group `L_0` is a constant
binary matrix.  Hence `L` does not normalize `L_0`, and uniqueness of the
finite group-algebra support gives

```text
LQL^(-1) != Q.                                        (MBT4)
```

It also misses the native target.  On `(7,8)`, the first native Whitehead
is

```text
J_1=[[1-q_0,y_1],[x_1,1-e_00]],
x_1=s_00t_0,  y_1=s_0t_00,  e_00=s_00t_00.           (MBT5)
```

For `g=J_1^(-1)L`, the eighth row of `g^(-1)=LJ_1` is

```text
(x_1,1-e_00,r)
```

on `(7,8,9)`.  Therefore

```text
g h g^(-1)=x_27(x_1)x_28(1-e_00)x_29(r),             (MBT6)
```

which again is not in the constant group `L_0`.  Thus `g` does not
normalize `L_0`, and

```text
LQL^(-1) != J_1QJ_1^(-1)=t_1Qt_1^(-1).              (MBT7)
```

The visible `x_29(r)` term cannot be repaired by simply cancelling its
unique factor.  Indeed `(MBT2)` factors as

```text
L=x_89(r) W,       W=W_79(1,q_1),                    (MBT8)
```

so left multiplication by `x_89(r)` leaves `W`.  But for the positive
signed generator `n=x_79(1) in L_0`, direct conjugation gives

```text
WnW^(-1)=x_79(q_0)x_97(q_1),                         (MBT9)
```

again outside the constant group.  Also, for
`g'=J_1^(-1)W`, the eighth row of `(g')^(-1)=WJ_1` is
`(x_1,1-e_00,0)`, so `g'` does not normalize `L_0`.  Thus the obvious
one-root cancellation still reaches neither Hecke target.

Consequently the most direct attempt to cancel the mixed-braid spectator
fails `(ESB1)` for both possible Hecke targets.  The calculation does not
say that the spectator can never be returned by a longer full-EL20 word;
it sharply closes only the bare relative aggregate-braid/cross-Whitehead
comparison.

No Property `(T)`, trace hypothesis, stability theorem, canonical
microstate profile, or local computation is used.

DERIVATION
mixed-braid-relative-target-proof

## Attempts

- **Use the positive occurrence `U'=x_79(1) in L_0`.**  It is indeed the
  identity on `QH`, and because `[U,U']=1`, also on `UQU^(-1)H`.  This does
  not type its later occurrences after the `V,V'` legs of the braid.  The
  exact relative word `(MBT2)` records the resulting chart change and
  exposes the nonconstant `x_29(r)` term in `(MBT3)`.
- **Compare directly with the native Whitehead target.**  Multiplication by
  `J_1` leaves the same nonconstant ninth-coordinate term in `(MBT6)`, so
  the comparison is not repaired by the already known native transporter.
- **Cancel the exposed `x_29(r)` contribution.**  The exact factorization
  `(MBT8)` reduces this to one partial Whitehead, but `(MBT9)` exposes its
  nonconstant action on the positive root `x_79(1)`.
