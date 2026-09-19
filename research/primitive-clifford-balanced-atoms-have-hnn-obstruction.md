---
rg: 2
id: primitive-clifford-balanced-atoms-have-hnn-obstruction
kind: claim
title: The balanced Clifford atoms admit an abstract HNN match but not the odd Whitehead match
distinct_from:
  finite-character-idempotents-have-exact-hnn-transport: that gives exact transport for arbitrary matched finite characters; this supplies the explicit controlled-Clifford source and target characters and proves why the transporting isomorphism cannot also be the odd Whitehead action.
  odd-row-unoriented-fine-return-has-quarter-floor: that gives the quantitative Hilbert--Schmidt floor for arbitrary matrices; this computes the exact finite-subgroup character geometry behind it.
  primitive-clifford-type-fixes-orientation-not-return: that uses the primitive central idempotent abstractly; this rewrites the source and trace-balanced target as signed Reynolds atoms of elementary abelian subgroups.
---

**ESTABLISHED.**  Use the diagonal Pauli convention

```text
e=(1-Z_1)/2,
f=((1-Z_1)/2)((1-Z_2)/2),
C=1-2f.                                                (PBA1)
```

In the controlled group `G_CZ`, put `a=tZ_2`.  Since the controlled
automorphism fixes `Z_2`, the subgroup

```text
H_s=<J,Z_1,a> ~=C_2^3                                (PBA2)
```

is abelian.  Let its character be

```text
chi_s(J)=-1,          chi_s(Z_1)=-1,       chi_s(a)=+1.
```

On the positive spin extension, `a=CZ_2` is `+1` on the whole coarse atom
`e`; on the negative extension it is `-1` there.  Therefore its signed
Reynolds projection is exactly

```text
p_s=e_(H_s,chi_s)=e z_+.                              (PBA3)
```

Likewise

```text
H_t=<J,Z_1,Z_2> ~=C_2^3,
chi_t(J)=chi_t(Z_1)=chi_t(Z_2)=-1                     (PBA4)
```

has signed Reynolds projection

```text
p_t=e_(H_t,chi_t)=f(z_++z_-)=fQ.                      (PBA5)
```

Both have canonical trace `1/8`.  There is even an explicit
character-preserving isomorphism

```text
phi(J)=J,        phi(Z_1)=Z_1,        phi(a)=Z_1Z_2.   (PBA6)
```

Hence a new HNN stable letter for `phi` transports `p_s` to `p_t` exactly,
with no regular-trace compensation and with the standard dimension-free
finite-group covariance estimate.  This proves that equal capacity and an
abstract regular-safe finite-subgroup return are **not** the obstruction.

The transporter cannot simultaneously be the odd Whitehead word.  The odd
row requires

```text
W Z_1 W^*=t.                                          (PBA7)
```

Since `p_s` lies in the `Z_1=-1` space, `(PBA7)` sends it into the `t=-1`
space.  But `p_t=fQ` has a nonzero summand `fz_-`, and on that summand
`t=-C=+1`.  In the regular representation

```text
tau(fz_-)=1/16.                                       (PBA8)
```

Thus no character-preserving subgroup isomorphism implemented by the same
`W` can carry `p_s` onto `p_t` while satisfying `(PBA7)`.  Equivalently,
any target signed-character subgroup whose projection is all of `fQ` cannot
contain `t`, because `t` is not scalar on `fQ`.

This is the exact representation-theoretic obstruction to replacing the
remaining matrix theorem by a literal finite-subgroup HNN edge.  A separate
HNN letter can transport the trace-balanced atoms, and the Whitehead word
can satisfy the odd conjugacy, but identifying the two letters recreates
the positive `1/16` wrong-orientation block.  The robust size of that block
is precisely the quarter-type floor in
`odd-row-unoriented-fine-return-has-quarter-floor`.
