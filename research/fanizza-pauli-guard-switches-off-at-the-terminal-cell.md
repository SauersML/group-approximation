---
rg: 2
id: fanizza-pauli-guard-switches-off-at-the-terminal-cell
kind: claim
title: The Fanizza Pauli guard switches off at the terminal cell and cannot be imposed globally
invalidates:
  - fanizza-native-join-tree-groupification-route
distinct_from:
  fanizza-c18-residual-factors-through-three-tiny-rank-gates: its full six-bit factorization is valid; only its optional native specialization obtained by setting the parity guard identically active is false.
  fanizza-native-additive-incidence-is-one-triangle: its unreduced four-context incidence calculation keeps the terminal guard and remains the correct native incidence audit.
  msz-clifford-machine-skeleton-has-polynomial-fillings: that records the preterminal/terminal commutator schedule abstractly; this evaluates the schedule in Fanizza's exact HALT representation and shows why the guard is load-bearing.
---

The identity

```text
X_tilde Z_tilde X_tilde Z_tilde=J                    (FTG1)
```

is not a defining relation of the Fanizza--Kroell--Mehta--Paddock--Rochette--
Slofstra--Zhao algebra.  The defining nonlinear relation is the guarded
product (relation (R6) of Mehta--Slofstra--Zhao, retained as `(R~6)` by
Fanizza et al.; `msz-guarded-projection-recurrence-is-relation-r6`)

```text
(P+X_tilde P X_tilde-U P U^*)
  (1+J X_tilde Z_tilde X_tilde Z_tilde)=0.            (FTG2)
```

Moreover `(FTG1)` is false in the exact marked HALT representation used for
completeness.

Suppose the machine halts after `n` steps.  In that representation,
`X_tilde,Z_tilde` are block diagonal over the cyclic cells
`i=0,...,n`, with blocks `X_(m,i),Z_(m,i)`.  The machine group relations give

```text
X_(m,i) Z_(m,i) X_(m,i) Z_(m,i)=J,   0<=i<n,
X_(m,n) Z_(m,n) X_(m,n) Z_(m,n)=1.                 (FTG3)
```

Therefore

```text
X_tilde Z_tilde X_tilde Z_tilde
 = diag(J,...,J,1),                                  (FTG4)
```

on each of the two cyclic-shift summands, whereas `J` acts as
`diag(J,...,J,J)`.  The terminal block of their difference is `1-J`, which is
nonzero in the canonical marked model.  With the normalized trace used in the
HALT construction,

```text
||X_tilde Z_tilde X_tilde Z_tilde-J||_2^2
 = 2/(n+1)>0,                                         (FTG5)
```

because the canonical group trace has `tau(J)=0`.  Only positivity is needed;
the displayed value also makes the failure quantitative.  (Checked against
the source 2026-08-22: in the Lemma 4.10 / Proposition 5.13 model `pi` is
the GNS representation of the canonical trace of `C H_L`, on which `J` is
not scalar, the cells `H_0 (x) E_(i,i)` all carry mass `1/(n+1)`, and the
marked projections `P_i <= (1-J)/2` occupy the `J = -1` corner; the
terminal block `pi(1-J) (x) E_(n,n)` therefore has squared normalized HS
norm `tau(2 - 2J)/(n+1) = 2/(n+1)`.  Restricted to the `J = -1` corner
alone the same block would contribute `4` per unit of mass; that corner
restriction is not the model used here.)

This is not an accidental defect of the model.  At the terminal cell the
second factor of `(FTG2)` becomes

```text
1+J,                                                   (FTG6)
```

which annihilates the marked `J=-1` carrier.  That switch permits the cyclic
recurrence to close even though the terminal commutator is `1` rather than
`J`.  On the preterminal cells the commutator is `J`, so the same factor is
`2` and the projection recurrence is enforced.  The guard is exactly the
halting switch.

If `(FTG1)` were added as an ordinary group relation, the guard factor would
be `1+J^2=2` on every cell and `(FTG2)` would force the unguarded recurrence at
the terminal cell as well.  The exact marked HALT representation would no
longer extend.  Consequently C18 cannot be replaced by the three-bit
recurrence in the native groupification problem, and the chord through
`Z_tilde` cannot be deleted by this argument.  The live native incidence is
the original one-triangle system, with the even-parity guard retained as a
genuine variable condition.
