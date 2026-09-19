---
rg: 2
id: atlas-six-relator-factor-retains-half-nontrivial-s3-mass
kind: claim
title: The exact six-relator Leavitt factor retains at least half its mass in nontrivial S3 channels
distinct_from:
  atlas-six-relator-leavitt-tracial-countermodel: that proves the five additive circulations retain energy when all six multiplicative rows vanish; this computes an explicit half-mass lower bound in the sign-plus-standard conjugation channels of the common relative unitary.
  atlas-19243-forces-sign-or-standard-channel-mass: that gives small positive constants in every finite microstate from collision; this gives the much larger exact-factor value and uses it to refute universal boundary charging.
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out a universal Hall-deficient support graph; this rules out the earlier universal step of making all eight nontrivial S3 sources small from the six row defects.
  atlas-five-row-operator-phase-lift: that asks for a finite-matrix-only nonlinear-to-linear estimate; this proves why its category qualifier remains indispensable after channel localization.
---

In the canonical Leavitt group factor model of the two regular `A8` charts,
choose an internal relative unitary `U` implementing the second chart from
the first.  Decompose `U` under diagonal conjugation by the collision subgroup
`K=<h_a,h_b>~=S3` as in `(CSM1)`.  Then all six Atlas rows vanish exactly,
but

```text
m_epsilon+m_sigma >= 1/2.                              (FHM1)
```

Consequently at least one of the eight reduced nontrivial `S3` operator
sources has normalized Hilbert--Schmidt mass at least `1/16`.

Indeed the two marked `A8` subgroups intersect trivially in the binary
Leavitt group.  For each nonidentity `h in {h_a,h_b}`, the bridge

```text
i_2(h)i_1(h)^(-1)
```

is therefore nonidentity.  Canonical group trace gives squared
Hilbert--Schmidt distance `2` from the identity.  If `rho=i_1`, right
multiplication of the covariance residual by `U^*` gives
`i_1(h)i_2(h)^(-1)`, which has the same trace and norm as the displayed
inverse bridge.  Hence the two covariance defects of `U` satisfy

```text
e(U)=a(U)^2+b(U)^2=4.                                  (FHM2)
```

The exact `S3` channel diagonalization used in `(CSM7)` gives

```text
e(U)<=8m_epsilon+6m_sigma
    <=8(m_epsilon+m_sigma),                            (FHM3)
```

which proves `(FHM1)`.  The eight-source pigeonhole is immediate.

This is a sharp category firewall for boundary transfer.  There is no fixed
constant `C` such that, in all finite tracial von Neumann algebras,

```text
m_epsilon+m_sigma
 <= C [sum_(j in {0,11,30,44,55}) ||pi_U(s_j)-1||_2^2
       +||pi_U(c_19243)-1||_2^2].                      (FHM4)
```

The right side is zero in this model and the left side is at least one half.
The same refutes any universal estimate making all eight reduced source
masses small from the six defects.

Thus the terminal typed localization cannot handle the sign branch by
universally charging it away, nor can it universally collapse the whole
standard channel.  It must use a genuinely finite-matrix rank/integrality
operation to transfer one positive source into the extension-labelled
`W,R0,R1,L0,L1` incidence, or exploit a relation which distinguishes an
admissible source while leaving the exact factor's residual mass elsewhere.
Merely projecting more universal six-relator consequences cannot provide
that step.
