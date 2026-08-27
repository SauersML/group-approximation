---
rg: 2
id: zpc-freezing-nonhyperlinear-route
kind: route
title: Readable-control freezing turns the perfect ZPC-IRS gap into a nonhyperlinear LCS solution group
target: non-hyperlinear-group
requires:
  - perfect-zpc-irs-quantum-gap-game
  - zpc-readable-control-freezing-to-lcs
  - finite-linear-commutation-system-to-lcs
  - perfect-lcs-gap-implies-nonhyperlinear
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
---

Take the finite tailored game `G` with a perfect ZPC-IRS strategy and
`omega*(G)<1/2`. Readable-control freezing supplies a global readable assignment
`r` whose frozen unconditional linear system has a perfect commuting operator
solution. The finite linear-commutation compiler turns that system into an
ordinary binary LCS `L(G,r)` without changing perfect operator solutions.

A perfect finite-dimensional strategy for `L(G,r)` would restrict to a perfect
finite-dimensional solution of the frozen unreadable system; adjoining the
fixed readable answers `r` would then give a perfect finite-dimensional
strategy for `G`, contradicting its quantum soundness gap. Therefore the LCS
has commuting value one and quantum value below one, and
`perfect-lcs-gap-implies-nonhyperlinear` gives a nonhyperlinear solution group.
