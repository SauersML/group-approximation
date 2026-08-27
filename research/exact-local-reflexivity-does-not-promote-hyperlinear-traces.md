---
rg: 2
id: exact-local-reflexivity-does-not-promote-hyperlinear-traces
kind: claim
title: Exactness and local reflexivity do not promote hyperlinear traces to MF traces
distinct_from:
  hyperlinear-trace-not-mf-trace: That supplies a hyperlinear non-MF trace on a separable unital algebra; this strengthens the counterexample by making the algebra exact, locally reflexive, and the trace faithful.
  exact-stably-finite-non-mf-reduced-group-algebra: That says one exact reduced group algebra is not MF as an algebra; this identifies its canonical trace as a faithful hyperlinear non-MF trace, which is a different and stronger trace-level statement.
  thom-kazhdan-central-fibre-hyperlinear-nonamenable: That adds property T and finite-dimensional invisibility but separates hyperlinear from amenable/quasidiagonal; this separates hyperlinear from MF using the repository's non-MF witness.
artifacts:
  - research/artifacts/cstar-regularity-trace-promotion-audit-2026-08-23.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**  There is a separable exact unital C-star algebra `A` with a
faithful tracial state `tau` such that `tau` is hyperlinear but is not an MF
trace.  Consequently the same holds with `A` locally reflexive.

Take `A=C*_r(W)` for the concrete exact sofic non-MF witness `W`.  Exactness,
separability, and faithfulness of the canonical reduced trace are established
by `exact-stably-finite-non-mf-reduced-group-algebra`.  Soficity makes its GNS
von Neumann algebra `L(W)` Connes embeddable, so the trace is hyperlinear.  If
it were MF, pullback along `C^*(W)->C*_r(W)` and
`regular-character-mf-trace-implies-group-mf` would make `W` operator MF, a
contradiction.  Kirchberg's theorem that exact C-star algebras are locally
reflexive gives the last assertion.

This rules out any Leavitt closure argument using only exactness or local
reflexivity of the full/reduced completion.  The missing upgrade from a
Connes-embeddable GNS algebra to finite-dimensional operator-norm trace models
is false even for a faithful trace on an exact algebra.
