---
rg: 2
id: raw-denominator-incidence-kills-off-diagonal-shell-orbit
kind: claim
title: Raw denominator incidence kills the off-diagonal forty-two-shell orbital escape
artifacts:
  - research/artifacts/sl3-raw-denominator-shell-incidence-2026-08-22.md
distinct_from:
  two-equivariant-shell-pvms-have-independent-coordinate-escape: that makes every lattice-actor row exact while retaining off-diagonal orbital mass; this identifies the first denominator row it cannot satisfy and computes its exact payment.
  five-parahoric-overlap-saturations-give-global-shell-pvm: that assumes five abstract chart saturation deficits are small; this bounds each RAW saturation using fixed coset-section words and centrality of the native base projection.
  polar-compression-turns-band-mismatch-into-first-exit: that controls polar transitions between already selected conductor bands; this shows exactly what additional estimate must tie those decoded bands to the raw native lamp conjugates.
---

Fix a root chart `w_0`.  For a Weyl neighbor `w`, choose coset
representatives `c_(w,i) in C` and put

```text
a_i=c_(w,i)h_w,
b_i=c_(w_0,beta_w(i))h.                                (RDI1)
```

The canonical equality of the corresponding vertices in `C h C/C` says
that there is a fixed word `d_i in C` with

```text
a_i=b_i d_i.                                           (RDI2)
```

There are only `42` such identities, all in the fixed finitely presented
group `SL_3(Z[1/p])`; their word lengths and derivation areas are therefore
bounded once and for all.

Let `rho` be a matrix assignment and let `P` be a projection.  Define the
raw branch projections

```text
A_i=rho(a_i)P rho(a_i)^*,
B_i=rho(b_i)P rho(b_i)^*.                               (RDI3)
```

Put

```text
epsilon_i=||rho(a_i)-rho(b_i)rho(d_i)||_2,
zeta_i=||[P,rho(d_i)]||_2.                              (RDI4)
```

Then the elementary conjugation estimate gives

```text
||A_i-B_i||_2 <=2 epsilon_i+zeta_i,                     (RDI5)
```

and hence the raw authentication deficit satisfies

```text
Delta_raw=(1/2)sum_i||A_i-B_i||_2^2
 <=4 sum_i epsilon_i^2+sum_i zeta_i^2.                  (RDI6)
```

For presentation defect `delta`, fixed-area telescoping bounds every
`epsilon_i` by `C_sec delta`.  If `P` is the native base lamp projection,
the fixed centralizer relators similarly bound every `zeta_i` by
`C_cent delta`.  Thus

```text
Delta_raw <= C_raw delta^2                              (RDI7)
```

with a constant independent of matrix dimension, congruence depth, and
multiplicity.  In an exact representation the raw deficit is zero.

The estimate also transfers to decoded chart projections.  If
`P_(w,i),P_(w_0,beta i)` satisfy

```text
R_w=sum_i||P_(w,i)-A_i||_2^2,
R_0=sum_i||P_(w_0,beta i)-B_i||_2^2,                    (RDI8)
```

then three-term telescoping gives

```text
Delta_w <=(3/2)(R_w+R_0+2 Delta_raw).                  (RDI9)
```

Algebraically, the desired simple-neighbor shell inequality would follow if
the decoder proved

```text
R_w+R_0 <= C(firstExitMass+mixedRootEnergy).             (RDI10)
```

Weyl symmetry gives the other four star edges with the same finite maximum
of constants.

**Scope correction.**  For the native lamp data, `(RDI10)` is impossible.
Each raw lamp conjugate has trace `1/2` (and each positive two-lamp atom has
trace `1/4`), whereas a partial 42-atom PVM has total trace at most one.
`balanced-raw-lamp-orbit-cannot-approximate-shell-pvm` gives the exact floors
`20` and `19/2` for `R_w` already before adding `R_0`.  Thus `(RDI9)` is a
valid conditional inequality but not the correct decoder interface.  The
raw incidence must instead be transferred to mutually orthogonal JOINT
spectral atoms of the raw lamp algebra.

## Exact payment on the independent-coordinate escape

For the coordinate PVMs on `Omega times Omega`, put

```text
R_diag=sum_i P_iQ_i.
```

The projections commute and a pointwise calculation gives the exact
square-function identity

```text
sum_i(P_i-Q_i)^2=2(1-R_diag).                           (RDI11)
```

Therefore, on every carrier operator `S`,

```text
sum_i||(P_i-Q_i)S||_2^2=2||(1-R_diag)S||_2^2.           (RDI12)
```

Zero raw incidence forces the carrier range into the diagonal subspace,
whose normalized trace is exactly `1/42`.  Thus the countermodel of
`two-equivariant-shell-pvms-have-independent-coordinate-escape` cannot be
extended across `(RDI2)` while retaining its full carrier: its off-diagonal
mass pays exactly, rather than merely through a spectral-gap estimate.

This proves the raw denominator incidence but does not by itself produce a
shell PVM.  The correctable-sector problem is to decode orthogonal
cylinder/character atoms from the joint raw lamp algebra and charge their
covariance loss to first exits.  Pointwise decoded-to-raw proximity is ruled
out.  Nothing here addresses the uniformly noncorrectable
`SL_3(Z)`-vertex sector.

There is, however, no remaining analytic obstacle in transferring the raw
section word **after** equal-rank decoded atoms have been constructed.
`equal-rank-denominator-edges-authenticate-decoded-atoms` uses
`T_i=rho(b_i)^*rho(a_i)` directly and proves

```text
(1/2)sum_i||Ehat_i-F_i||_2^2
 <=2 sum_i firstExit_i+2 sum_i pvmCovariance_i
    +C_sec delta^2.                                    (RDI13)
```

This replaces the impossible decoded-to-raw proximity target `(RDI10)`.
The remaining extraction gate is exactly to construct equal-rank joint
atoms for which the first two terms in `(RDI13)` belong to the established
conductor and full-PVM covariance ledgers.
