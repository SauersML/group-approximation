---
rg: 2
id: leavitt-range-sum-fold-does-not-pay-reynolds
kind: claim
title: The scalar Leavitt range-sum fold does not pay transverse Reynolds leakage
distinct_from:
  carrier-not-decoder: that uses one finite UT4 packet to show a common long-root carrier need not classicalize its outer inputs; this couples two central-character UT4 packets to the exact rectangular Weyl cell and preserves the full Reynolds leakage while the range-sum fold is exact.
  leavitt-range-sum-fold-is-first-object-erasing-row: that identifies the first native word which leaves the typed Morita path language; this proves that the word alone still does not identify the coefficient occurrences with the packet multiplicity reservoir.
  leavitt-branch-reynolds-return-has-rectangular-gap: that computes the leakage of the branch Reynolds operator; this supplies an exact packet-plus-fold model retaining that leakage.
---

**ESTABLISHED COUNTERMODEL.**  Fix odd `p`, a nontrivial `p`th root `zeta`,
and the exact rectangular Weyl cell on `K=C^p tensor C^p` from
`first-leavitt-weyl-cell-has-exact-rectangular-model`.  Its source and
two-child packets, branch transports, and common scalar mark are exact, and

```text
||(I-R_1)Ad(U_0)R_s||_(HS,ad)^2=p^(-2)-p^(-4).          (FRN1)
```

Let `N=UT_4(F_p)` and put

```text
a=e_12(1),       h=e_23(1),       b=e_34(1),
z=e_14(1).
```

Then `a` and `b` commute, `z` is central, and, after changing one generator
to its inverse if required by the commutator convention,

```text
[a,[h,b]]=z.                                            (FRN2)
```

The `zeta` spectral subspace of `z` in the left regular representation of
`N` is nonzero and invariant.  On it, `(FRN2)` is the scalar `zeta I`.

Take two independent copies `N_D,N_C` of this central-character
representation and tensor them with `K`.  Use the product of the two middle
elements as the single middle-root unitary.  For the diagonal path `D`, use
the outer elements `a_D,b_D`; for the first range path `C_0`, use
`a_C,b_C`; and make the second range path `C_1` trivial.  All left outer
elements commute with all right outer elements: within each copy this is
`[e_12,e_34]=1`, and across copies it is tensor independence.  Yet

```text
D=zeta I,             C_0=zeta I,             C_1=I,
C_0C_1D^(-1)=I.                                        (FRN3)
```

Identify the common marked central phase with the same scalar `zeta I`.
The auxiliary UT4 factors commute with the rectangular Weyl packet, so they
do not change any Reynolds operator or `(FRN1)`.  Therefore the packet,
branch covariance, commuting-outer-root geometry, nontrivial marked phase,
and the scalar fold word are all exact while the transverse leakage remains
the fixed positive value `p^(-2)-p^(-4)`.

Consequently no estimate of the form

```text
leakage <= omega(||r_fold(U)-I||_2, packet defect)       (FRN4)
```

with `omega(0,0)=0` can hold from those data alone.  The fold detects only
the product of three long-root outputs.  A viable full-presentation decoder
must additionally synchronize the **occurrences** of `s_i,t_i` in the fold
with the branch coefficient maps whose multiplicity Reynolds ranges are
being compared.  Equivalently, it needs a payload-coupled occurrence
relation or finite-coordinate conditional map; equality of the scalar
output root, even on a nontrivial common phase carrier, is insufficient.
