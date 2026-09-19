---
rg: 2
id: phase-tagged-row-defect-reduces-to-within-type-selector-mismatch
kind: claim
title: Phase-tagged row domination reduces exactly to within-type selector mismatch
distinct_from:
  global-marked-type-cycle-selector-decoder: that consumes a summed GTC4 row estimate once supplied; this separates one row into a phase-controlled wrong-type term and the irreducible matched-type term.
  compressed-k2m-deficit-is-one-aggregate-sign-row: that compresses the K_(2,m) capacity deficit to one binary covariance; this identifies the general projection-theoretic split behind such a covariance.
---

Let `e<=Q_s` and `f<=Q_t` be projections in a finite tracial algebra and let
`U` be unitary.  Put

```text
L=||(1-Q_t)Ue||_2^2,
I=||Q_t UeU^* Q_t-f||_2^2.                              (PTR1)
```

Then

```text
||UeU^*-f||_2^2 <=4L+2I.                               (PTR2)
```

Consequently, for a finite family of marked rows, if authenticated
two-sided phase tags give

```text
sum_omega ||(1-Q_(sigma(omega)))U_omega Q_omega||_2^2
 <=C_tag E_word+o(1),                                  (PTR3)
```

then

```text
sum_omega d_omega^2
 <=4C_tag E_word+2 sum_omega I_omega+o(1),              (PTR4)
```

where

```text
I_omega=
 ||Q_(sigma(omega))U_omega e_omega U_omega^*
   Q_(sigma(omega))-f_(sigma(omega))||_2^2.             (PTR5)
```

Thus finite phase covariance closes the cross-type population part of GTC4.
The remaining matrix-only assertion is entirely inside the already matched
target type.  Phase tags do not by themselves authenticate the nonlinear
forbidden-weighted selectors occurring in `(PTR5)`.

