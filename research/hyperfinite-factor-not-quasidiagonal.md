---
rg: 2
id: hyperfinite-factor-not-quasidiagonal
kind: claim
root: true
title: The hyperfinite II1 factor is not quasidiagonal (negation of STW Problem X(2))
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that is the positive side of Problem X(2); this is its negation, carried separately because a route into it now exists.
  stw99-problem-x1-fails-on-full-group-algebras: that refutes X(1) through an amenable non-quasidiagonal canonical trace on some full group algebra C*(G); this refutes X(2), which is the single trace of R, and it also refutes X(1) but through the trace of R rather than a group trace.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

The hyperfinite II₁ factor `R` is not quasidiagonal as a C\*-algebra;
equivalently (unique faithful trace) `τ_R` is an amenable trace that is not
quasidiagonal.  Establishing this refutes Problem X(2) and, through
`stw99-x1-implies-x2`, Problem X(1) of Schafhauser--Tikuisis--White,
arXiv:2506.10902.

Live route: `hyperfinite-factor-not-qd-via-non-mf-unitary-subgroup`, which
needs one countable non-MF group inside `U(R)`.

## Attempts

* Group witnesses: see `non-mf-subgroup-of-hyperfinite-factor-unitary-group`.
  Kazhdan witnesses are dead; the literal group `E` and the Clifford
  witnesses are dead too (`literal-group-mark-invisible-to-hyperfinite-representations`,
  `clifford-witness-has-no-hyperfinite-marked-representation`).  No known
  non-MF group remains as a candidate; a witness needs a non-MF certificate
  that survives hyperfinite representations.
* Non-group witnesses: any separable non-quasidiagonal `A` with a faithful
  trace of hyperfinite GNS closure.  `A` cannot be the reduced C*-algebra of
  a nonamenable group, so Rosenberg's non-quasidiagonality mechanism is
  unavailable (`nonamenable-reduced-group-algebras-avoid-hyperfinite-gns`).  By Tikuisis--White--Winter and Gabe such
  an `A` is not both exact and UCT (recorded by the peer lane in
  `stw99-problem-x2-hyperfinite-factor-quasidiagonal`).  Residually
  finite-dimensional algebras such as `C*(F_2)` do embed in `R` but are
  quasidiagonal, so non-exactness alone is not enough; the witness must be
  non-quasidiagonal for a reason invisible to all its finite-dimensional
  representations, which is exactly what a non-MF group supplies.
