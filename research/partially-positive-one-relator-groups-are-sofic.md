---
rg: 2
id: partially-positive-one-relator-groups-are-sofic
kind: claim
title: Every one-relator group with a partially positive relator is residually solvable and sofic
distinct_from:
  residually-rationally-solvable-one-relator-sofic: that assumes residual solvability for the rational derived series and then proves soficity abstractly; this supplies a syntactic condition on the relator yielding ordinary residual solvability, which need not be residual rational solvability.
  one-relator-abelian-linton-radical-sofic: that allows a nontrivial abelian Linton radical with no sign condition on the relator; this starts from a one-sided occurrence condition on one generator and concludes the stronger property of residual solvability.
  berlai-perfect-linton-radicals-are-sofic: that treats explicit non-residually-solvable groups with perfect Linton radical; this treats the opposite, residually solvable, side through partial positivity of the relator.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

A reduced word `w` in a free group `F(X)` is **partially positive** if some
generator `a` occurs in `w` but `a^(-1)` does not.  For every such word,

    G = F(X)/<<w>>

is residually solvable.  Consequently it is residually amenable and sofic.

This strictly extends the classical positive-relator family: all other
generators may occur with both signs.
