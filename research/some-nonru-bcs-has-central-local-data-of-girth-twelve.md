---
rg: 2
id: some-nonru-bcs-has-central-local-data-of-girth-twelve
kind: claim
title: Some Boolean constraint system without R^U models admits finite local data of incidence girth twelve whose variable subgroups meet pairwise in the phase
distinct_from:
  tracial-nonru-bcs-has-phase-surviving-local-colimit: that asks for phase survival for the fixed MIP* source; this asks only for local data of a combinatorial type for which survival is automatic, for any non-RU source.
  central-local-data-of-incidence-girth-twelve-keeps-the-phase: that proves survival for such local data; this asks whether a non-RU source admits such local data at all.
  mipstar-bcs-tracial-nonru-exists: that supplies a tracial non-RU source with no control on its incidence graph; this asks for a non-RU source whose incidence graph has girth at least twelve and whose contexts admit centrally intersecting finite readouts.
---

**OPEN.** Does there exist a finite Boolean constraint system `B`, not
`R^U`-satisfiable (no unital *-homomorphism `A(B) -> R^U` into a tracial matrix
ultraproduct), together with finite local data `D` for `B` and some `n >= 2` in
the sense of `finite-readout-bcs-decoders-are-phase-surviving-local-colimits`,
satisfying (G12), (CI) and (PR) of
`central-local-data-of-incidence-girth-twelve-keeps-the-phase`?

A positive answer gives a nonhyperlinear group through
`nonhyperlinear-group-via-central-girth-twelve-local-data`. Tracial
satisfiability of `B` is not assumed; it follows.

## Constraints on any witness

- **Nonscalar variables cannot be copied.** Contexts that force a variable to
  be a function of another violate (CI), by (CN2) of
  `commuting-nonscalar-readouts-force-coset-four-cycles`. So the incidence girth
  of the source cannot be raised by equality or negation subdivision (CB3).
- **Short cycles are already fatal for barycentric certificates.**
  `barycentric-curvature-certificates-need-incidence-girth-eight` needs at least
  four contexts per cycle of nonscalar variables.
- **Affine-unsafe contexts need nonabelian local groups.** Where the source's
  supports are affine-unsafe, abelian group-element readouts are excluded
  (CS2), as recorded on `tracial-nonru-bcs-has-phase-surviving-local-colimit`.
- **A consistency test with no known answer.** If `B` is not tracially
  satisfiable, no such local data exists. For example, a linear system with no
  operator solution admits no local data with (G12), (CI), (PR). So any general
  construction of such local data must detect tracial satisfiability.

## Attempts

1. **Lifts of the incidence graph (untested).** Graph covers of `Inc(B)` raise
   girth, and a perfect model of `B` gives one of the cover by copying operators.
   But an `R^U` model of the cover need not assign equal operators to copies, so
   non-`R^U`-ness of the cover is not inherited. Soundness under lifts is the
   missing input.
