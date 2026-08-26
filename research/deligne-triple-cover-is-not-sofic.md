---
rg: 2
id: deligne-triple-cover-is-not-sofic
kind: claim
title: Deligne's triple cover of Sp4(Z) is not sofic
distinct_from:
  kt-pair-group-double-is-nonsofic: that is an established nonsoficity theorem for a compressed Kazhdan pair; this is an open nonsoficity statement for an arithmetic central extension with no compressor, whose only known mechanism is the Gohla--Thom cohomological one.
  gohla-thom-stable-base-nonsofic-extension: that is the conditional external theorem; this is its would-be instance at `Sp_4(Z)` with `A = Z/3`, whose hypotheses (stability in finite actions and the cosystolic inequality) are open for this base.
  literal-group-not-sofic: that asks about this repository's non-MF group, which is sofic; this asks about Deligne's classical extension.
artifacts:
  - research/artifacts/thom-0810-2180-verified.md
---

OPEN (two-sided by design).  Claim: Deligne's triple cover `E_3` of
`Sp_4(Z)` is not sofic.

**Stakes.**  `E_3` is finitely presented, Kazhdan, not residually finite, and
its hyperlinearity is open in both directions in this graph.  With
`deligne-triple-cover-is-hyperlinear` it would give the Pestov 3.4 separation
(`hyperlinear-nonsofic-from-deligne-triple-cover`); with the lane's
non-hyperlinearity routes it would instead be a non-sofic non-hyperlinear
group, and either way settles `E_3`.  Settled negatively (`E_3` sofic), it
would be a sofic Kazhdan non-residually-finite group of a new kind (Thom's
example of that phenomenon is LEF, arXiv:0810.2180), and it would refute the
Gohla--Thom hypotheses for `Sp_4(Z)`.

## Attempts

- **Gohla--Thom mechanism** (`deligne-triple-cover-nonsofic-via-gohla-thom`).
  Theorem 3.13 of arXiv:2403.09582 gives nonsoficity of a non-residually-finite
  central extension by a finite abelian `A` when the base is residually
  finite of finite type (true for `Sp_4(Z)`), satisfies a dimension-two
  cosystolic inequality for finite transitive actions with `A`-coefficients,
  and is stable in finite actions (their Definition 3.7, a permutation
  notion much weaker than flexible stability).  Both hypotheses are open for
  `Sp_4(Z)` (`sp4-z-satisfies-gohla-thom-hypotheses`); the cosystolic input
  is known only for torsion-free lattices in `PSp_(2d)(Q_p)`, `d >= 4`, `p`
  large (Kaufman--Kazhdan--Lubotzky, Evra--Kaufman), where
  Chapman--Dikstein--Lubotzky apply it.  Becker--Lubotzky's non-P-stability
  of residually finite `(tau)` groups does not refute the weak notion.
- **Compression mechanism.**  No compressed Kazhdan pair inside `E_3` is
  known; `Sp_4(Z)` is a lattice and its commensurated subgroups are
  incompressible in the sense of the arithmetic lane, so Kun--Thom-type
  arguments have nothing to act on.
- **Finite-dimensional invisibility is not nonsoficity.**  Every finite
  quotient and every finite-dimensional unitary representation kills `z`
  (`deligne-triple-cover-fd-central-invisibility`), so any sofic
  approximation must be far from finite quotients; this is a constraint,
  not an obstruction (`finite-quotient-blindness` is the analogous remark
  for compressed pairs).
