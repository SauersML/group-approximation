---
rg: 2
id: toric-clause-spectra-cannot-generate-monomial-factor
kind: claim
title: Phase-safe toric clause spectra cannot generate a factorial monomial game algebra
artifacts:
  - research/artifacts/monomial-toric-factor-clause-audit-2026-08-23.md
distinct_from:
  toric-gap-is-a-relative-fd-central-word-face: that computes the abstract normal quotient; this applies its centralization directly to the Fourier generators of a monomial game and uses an extreme trace to prove the generator-visible no-go.
  finite-morita-toricization-cannot-encode-nonaffine-support: that uses finite-group induction and centers to exclude nonlinear answer supports; this permits arbitrary infinite player groups and needs only that the monomial Fourier generators be spectra of clause components.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that shows a raw projective kernel need not have a finite-dimensional face gap; this proves why direct clause spectra cannot avoid that projective-kernel step.
---

**ESTABLISHED.**  Let `Gamma=B x G_A x G_B` and let a full tracial
representation satisfy toric clauses

```text
beta_t a_t b_t=1,       a_t in G_A, b_t in G_B.       (MTC1)
```

If `M_A` and `M_B` are the two commuting player von Neumann algebras in the
trace GNS image, then

```text
rho_A(a_t) in Z(M_A),        rho_B(b_t) in Z(M_B).     (MTC2)
```

Indeed `(MTC1)` gives
`rho_A(a_t)=conjugate(beta_t)rho_B(b_t)^*`; the right side commutes with
`M_A`, and symmetrically for Bob.  In particular, in a factorial player
model every clause component is scalar.

Let `A_mon` be a finite-phase monomial game algebra with a tracial state but
no nonzero homomorphism into `R^omega`.  Its Fourier/sudoku projections

```text
e_(ki)^p=(1/s) sum_r zeta^(-rp)u_(ki)^r              (MTC3)
```

generate `A_mon`.  There is no phase-safe full-corner toric model in which
all these projections belong to the spectral algebra of the clause player
components and generate the corner.  By `(MTC2)` their images would be
central, so the corner would be commutative.  Choosing an extreme trace makes
the GNS algebra a factor; a commutative factor is `C` and gives a character
`A_mon -> C -> R^omega`, contradicting the gap.

The group-quotient version is identical: normal closure centralizes every
player clause component, so its compressed spectral projections remain
central in every full corner.  Therefore promoting the Fourier projections
to independent cyclic clause letters, or using them directly as clause
spectra, cannot groupify the monomial gap.

This does not rule out a compiler whose Fourier projections are decoded from
other **noncentral** words while its clauses constrain separate central
shadows.  Such a compiler must prove a whole-face decoder; local answer-table
preservation is insufficient.
