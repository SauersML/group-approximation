---
rg: 2
id: atlas-word-fiber-secants-have-full-multiplicity-absorber
kind: claim
title: Exact Atlas word-fiber secants retain the full aligned multiplicity reservoir
distinct_from:
  atlas-aligned-word-jacobian-has-full-multiplicity-absorber: that treats first derivatives at an aligned frame; this treats finite nonlinear chords inside the exact common word-evaluation fiber.
  atlas-full-relator-data-factor-through-double-commutant-gauge: that proves equality or conjugacy of relator evaluations under double gauge; this computes the linear span and mixed-block ranges of the resulting exact fiber secants.
  atlas-phase-jacobian-has-invertible-gauge-kernel: that gives an infinitesimal scalar tangent; this gives an exact finite chord reservoir containing arbitrary multiplicity matrices.
---

**ESTABLISHED NONLINEAR-SECANT FIREWALL.**  Fix any relative frame `U` and
any finite family `W` of alternating Atlas words.  For every unitary

```text
C in rho_2(A8)'
```

all conjugated second-chart letters are unchanged under `U -> UC`.  Hence

```text
pi_(UC)(w)=pi_U(w)             for every w in W.             (AFS1)
```

The exact common word-evaluation fiber through `U` therefore contains its
whole right-commutant orbit.  The complex linear span of its chords contains

```text
span_C{UC-U:C unitary in rho_2(A8)'}
   =U rho_2(A8)'.                                             (AFS2)
```

The equality uses the fact that a finite-dimensional unital C-star algebra
is linearly spanned by its unitaries; the identity itself is already a chord
direction because `C=-I` gives `UC-U=-2U`.

At an aligned regular frame `U_0`, decompose as in
`atlas-aligned-word-jacobian-has-full-multiplicity-absorber`.  On every
aligned irreducible block, `(AFS2)` is

```text
A_sigma tensor Hom(M_sigma,M_(alpha sigma)).                 (AFS3)
```

Consequently every nonzero minimal-Fourier coefficient of `A_sigma` again
has full collective target multiplicity range.  The fiber-secant space also
contains the invertible operator `U_0`, so it has no shrunk subspace at all.

Thus replacing the ordinary Jacobian by the span of exact nonlinear secants
does not rescue the Atlas range route.  Any surviving nonlinear
singular-space certificate must use *quantitative variation transverse to*
the exact double-commutant fiber--not merely which frames have the same word
values, nor the linear span of differences between them.  In particular a
zero-fiber minor assembled from `q_u(R_j(UC)-R_j(U))p_v` is identically zero
on a full multiplicity reservoir and cannot authenticate a proper common
range.

