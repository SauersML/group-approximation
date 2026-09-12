---
rg: 2
id: linear-decoders-over-leavitt-units-admit-no-measurable-section
kind: claim
title: No linear decoder over the Leavitt units into a larger alphabet admits a measurable equivariant section
distinct_from:
  measurable-alphabet-compression-over-leavitt-units: that is the existence of any almost everywhere injective code into fewer symbols; this is the obstruction side restricted to codes whose decoder is linear over a finite field, where a section is exactly such a compression.
  linear-decoders-with-coboundary-functionals-admit-no-section: that excludes sections for decoders with a coboundary functional or finite nonzero kernel, over every group; this asks for all linear decoders over the Leavitt units.
artifacts:
  - research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md
---

**OPEN.** Let `U = L_(F_2)(1,2)^x`, `p` prime, `m < m'`, and `L: (F_p^m)^U -> (F_p^(m'))^U` a linear decoder. There
is no Borel equivariant `tau` with `L o tau = id` almost everywhere.

**Where it sits.**
- A section is an almost everywhere injective code from `p^(m')` symbols into `p^m` symbols, that is, a
  measurable compression. So maximal Bernoulli Rokhlin entropy over `U` implies the claim (route
  `linear-decoder-sections-excluded-by-maximality`).
- A continuous linear section is a pair `SR = I_(m')` over `F_p[U]`, a stable finiteness failure, and a
  continuous nonlinear section with continuous decoder is a strict automaton.
- The negation lies between stable finiteness failure and `measurable-alphabet-compression-over-leavitt-units`.
  It is the measurable relaxation of a linear one-sided inverse.

## Attempts

- **Coboundary functionals, annihilators, finite kernels.** Dead:
  `linear-decoders-with-coboundary-functionals-admit-no-section`. That covers every decoder with a two-term row
  along one element, including the ascended Ornstein–Weiss map, whatever the section reads along the rigid
  defect.
- **Zero kernel.** A section would be the continuous inverse, so it needs a stable finiteness failure over
  `F_p[U]`. That failure is open (`gottschalk-surjunctivity-conjecture` region, corner lanes).
- **What remains.** Decoders with infinite kernel, `q -> R*q` injective on finitely supported columns (a failure
  of the strong rank condition, which occurs over every group containing a free subgroup, such as `U`), and no output functional pulling back to
  a coboundary with nonzero coset sum. No construction and no obstruction is known. Even over `F_2`, where
  maximality excludes every section, it is not known whether Theorem K′ alone detects every decoder. Artifact
  Section 6.
