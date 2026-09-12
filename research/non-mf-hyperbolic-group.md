---
rg: 2
id: non-mf-hyperbolic-group
kind: claim
title: A word-hyperbolic group that is not MF
distinct_from:
  non-residually-finite-hyperbolic-group: non-MF implies non-residual-finiteness for the same group; the reverse implication between these existence questions requires an additional approximation argument
  relative-hull-quotient-with-full-mf-radical: that produces acylindrically hyperbolic Kazhdan groups with full MF radical, which are not word-hyperbolic in general; this demands word-hyperbolicity
---

Exhibit a word-hyperbolic group that is not operator MF (norm-matrix-corona
sense of `countable-group-mf-conventions`).

A witness would answer Gromov's residual-finiteness question negatively:
every countable residually finite group is operator MF, and hyperbolic
groups are countable. The converse existence implication was previously
claimed through weak quasidiagonality. The 2026-09-11 audit
`mf-to-weak-qd-citation-has-unproved-lifting-step` identifies the missing
completely positive approximation step in that argument. Therefore the
claimed equivalence with the residual-finiteness problem is not justified
by that citation. A proof that every hyperbolic group is operator MF is not
shown here to settle residual finiteness.

## Attempts

- **From a Kazhdan hyperbolic group without finite quotients.**
  `non-mf-hyperbolic-from-kazhdan-quotientless` is a valid conditional route
  requiring `mf-kazhdan-group-without-finite-quotients-is-trivial`. Its old
  justification did not establish that prerequisite. Ozawa--Thom directly
  gives failure of weak quasidiagonality instead.
- **The repository's non-MF mechanisms.**  The full-MF-radical witnesses here
  are produced by Hull's small cancellation and are only acylindrically
  hyperbolic (see `relative-hull-quotient-with-full-mf-radical`); word
  hyperbolicity is not preserved by those constructions (audit §B.7 in
  `research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md`).
  The Kun--Thom compression witnesses are excluded in a hyperbolic ambient
  group by the centralizer rigidity of audit §B.1.  Whether the operator-norm
  compression mechanism itself can run inside a word-hyperbolic group is not
  decided here.
