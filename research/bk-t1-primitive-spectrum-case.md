---
rg: 2
id: bk-t1-primitive-spectrum-case
kind: claim
title: Every separable nuclear stably finite C*-algebra with T_1 primitive ideal space is quasidiagonal
distinct_from:
  stw99-vii-restricted-to-simple-algebras: that is the simple case; this is the case of T_1 primitive spectra, which contains it and which the simple case implies.
  bk-primitive-quotients-qd-or-traceless-force-qd: that is the established fibrewise theorem; this is the T_1 case of Problem VII, still open in general and established when primitive quotients satisfy the UCT.
artifacts:
  - research/artifacts/bk-t1-spectrum-simple-reduction-2026-09-12.md
---

**OPEN in general; equivalent to the simple case.**  Let `E` be separable,
nuclear and stably finite, with every primitive ideal maximal, i.e. `Prim(E)`
is `T_1`.  Then `E` is quasidiagonal.

- **Implied by the simple case.**  Route `bk-t1-spectrum-from-simple-case`: the
  primitive quotients are simple.  Each is traceless or stably finite (artifact
  Fact T3).  If the simple case of Problem VII makes the stably finite ones
  quasidiagonal, `bk-primitive-quotients-qd-or-traceless-force-qd` applies.
- **Contains the simple case.**  A simple algebra has a one-point, hence `T_1`,
  spectrum.  So this claim is equivalent to
  `stw99-vii-restricted-to-simple-algebras`.
- **Established under the UCT.**  If every primitive quotient satisfies the UCT,
  the claim holds.  Examples: continuous fields over locally compact Hausdorff
  spaces with simple UCT fibres, mixing Kirchberg and classifiable stably finite
  fibres freely.

So for Hausdorff or `T_1` spectra, Problem VII carries no gluing difficulty
beyond the simple case.  By `stw07-qd-radical-criterion-compact-open` any
non-simple difficulty needs primitive ideals that are not maximal, i.e. prime
non-simple quotients carrying traces.
