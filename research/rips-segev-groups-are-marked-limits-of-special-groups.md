---
rg: 2
id: rips-segev-groups-are-marked-limits-of-special-groups
kind: claim
title: Each Rips--Segev group is a marked limit of torsion-free virtually compact special groups
distinct_from:
  rips-segev-groups-are-cocompactly-cubulated: that asks for a cubulation of the group itself; this asks only for approximation by special groups, which by finite presentation means quotients of the group that are special and injective on growing balls.
  marked-limits-of-special-groups-have-domain-group-rings: that is the general criterion; this is the approximation premise for one family.
---

**OPEN.** For every Rips--Segev torsion-free group `G` without unique products,
with a finite generating set `S`, the marked group `(G, S)` is a limit of
torsion-free virtually compact special marked groups.

**Equivalent form.** `G` is finitely presented, being hyperbolic
(`rips-segev-groups-are-hyperbolic`). So approximants are eventually quotients
of `G`: the premise says that for every `R` there is a quotient of `G` that is
torsion-free virtually compact special and injective on the ball of radius `R`.

**Obstruction for the generalized family.** By
`kazhdan-groups-map-trivially-to-torsion-free-special-groups`, the premise fails
for every infinite finitely presented property (T) group. That includes the
Kazhdan examples of Arzhantseva--Steenbock (arXiv:1407.2441).

**Candidate approximants.** Martin--Steenbock (arXiv:1409.3678) cubulate
quotients of free products of cubulable groups by finitely many relators that
satisfy the *classical* `C'(1/6)` condition. With torsion-free hyperbolic
factors, Agol then makes such quotients virtually compact special. A proof of
the premise would exhibit, for each `R`, a quotient of `G` admitting such a
presentation (over some free product) and injective on the ball of radius `R`.
No such quotient is known. Steenbock records that the Rips--Segev relators
"can have long common parts" (arXiv:1307.0981, introduction), which is exactly
what the classical condition forbids, so the presentation defining `G` itself
does not qualify.

## Attempts

Both attempts are from lane hl-rips-segev-limits, 2026-09-14; see
`research/artifacts/hl-rips-segev-limits-2026-09-14.md`.

1. **Truncations fail at the classical small cancellation hypothesis.**
   - A quotient `G/<<S>>` is presented by the defining relators together with
     `S`, so it keeps the long common parts. A classical `C'(1/6)` presentation
     of such a quotient would have to be an unrelated presentation, and none is
     known.
   - The other Martin--Steenbock hypotheses (finitely many cubulable factors,
     here `<a>` and `<b>`) are harmless. The failing one is classical `C'(1/6)`.
   - The malnormal special quotient theorem needs the ambient group to be
     virtually compact special already, so it is circular for this premise.
     Wise's statement was not pinned in this lane.
2. **The direct route reduces to wallspaces on graph cones.**
   - If `G` itself is virtually compact special, the constant sequence gives the
     premise. So `rips-segev-groups-are-cocompactly-cubulated` plus Agol
     suffices.
   - The cubical small cancellation route is
     `rips-segev-cubulation-via-b8-graph-cone-wallspaces`. Its open inputs are
     `rips-segev-graph-cones-admit-b8-wallspaces` and
     `b8-hyperbolic-cubical-presentations-cocompactly-cubulated`.
   - Any such wallspace must have the shape given by
     `b8-graph-cone-wall-classes-are-sparse-edge-cuts`.
