---
rg: 2
id: a1-corner-conjugacy-support-fence-proof
kind: route
title: Cancel the A1 tail inside the signed source corner
target: a1-corner-conjugates-do-not-enlarge-native-cross-support
requires:
  - full-q-a1-binary-extension-closes-zero-cross-block
  - full-q-separate-actor-packet-retains-zero-cross-central-block
  - row2-source-factor-detects-paid-pauli-sheet
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
---

The exact source calculation says `AQ=QA`.  The roots

```text
A=x_47(s_1t_0),       r=x_58(s_1t_00),
l=x_69(s_1t_000)
```

are pairwise nonincident, so `A` commutes with `r,l`.  Expanding
`F=Q(1+r)(1+l)/4` proves `(A1C2)`.

Since `A^2=1`,

```text
u=FAF=AF,
u^*u=FAA F=F=uu^*.                                   (1)
```

Thus `u` is a corner unitary.  Direct multiplication gives

```text
F(AgA)F=(FAF)(FgF)(FAF)=uhu^*.                       (2)
```

Inner conjugation preserves every two-sided ideal, proving `(A1C4)`.

For the common-tail formulas, use `AF=FA`:

```text
u_iF=v_iAF=v_iFA.                                     (3)
```

Therefore

```text
(u_iF)(u_iF)^*=v_iFAA Fv_i^*=v_iFv_i^*,              (4)
```

and

```text
(u_1F)^*(u_2F)
=AFv_1^*v_2FA
=(FAF)(Fv_1^*v_2F)(FAF)
=u(Fv_1^*v_2F)u.                                     (5)
```

Because `u=u^*`, equation `(5)` is unitary conjugacy in the `F`-corner.
This proves every support statement in `(A1C7)` without using a trace or a
finite quotient.

Finally the exact compression model `(SFD9)` has a projection called `Q`
which is the full signed source for that scoped table, commutes with `A`,
and satisfies `Q(K_A-1)Q=0` while `K_A` is mark-conjugate and nontrivial.
Represent the two additional positive signs `r,l` trivially on this scoped
table.  Then `F=Q(1+r)(1+l)/4=Q`, which proves `(A1C9)`.  This does not model
the complete `P_A` packet, so it is used only to exclude a certificate based
on normalization and global detector rank.  The canonical full-support
result must therefore spend one of the genuinely mixed rows in `(A1C10)`.
