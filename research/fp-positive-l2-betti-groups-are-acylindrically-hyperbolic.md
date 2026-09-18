---
rg: 2
id: fp-positive-l2-betti-groups-are-acylindrically-hyperbolic
kind: claim
title: Every finitely presented group with positive first L2-Betti number is acylindrically hyperbolic (Osin's problem)
distinct_from:
  fp-simple-group-with-positive-first-l2-betti-number: that asks for a finitely presented simple group with positive first L2-Betti number; such a group would refute this, since simple groups are never acylindrically hyperbolic.
  fpbs-minasyan-osin-weakly-malnormal-splittings: that imports the Minasyan–Osin criterion for splittings; this is Osin's open problem, whose solved case (groups mapping onto Z) combines that criterion with Peterson–Thom.
---

**OPEN.** Printed by D. Osin, *On acylindrical hyperbolicity of groups with positive first ℓ²-Betti number*,
arXiv:1501.03066 (Bull. LMS 2016), final section, TeX l.212–214, read at source 2026-09-18:

> Is every finitely presented group $G$ with positive first $\ell^2$-Betti number acylindrically hyperbolic?

**Known case (Osin's Theorem 1.1, l.80–82).** Yes if `G` also maps onto `Z`. Osin's Corollaries (l.87–98):
- finitely presented residually finite groups with `β_1^(2) > 0` are virtually acylindrically hyperbolic;
- finitely presented groups of deficiency at least 2 are acylindrically hyperbolic.

**Osin's own warning (l.216).** There are finitely presented groups with `β_1^(2) > 0` that do not virtually
map onto `Z`, e.g. `Q * Q` for a finitely presented infinite simple `Q`. "Thus there is no way to reduce the
general case of this problem to Theorem 1.1."

## Where it meets this graph

- **Simple groups.** Simple groups are never acylindrically hyperbolic (Minasyan–Osin, arXiv:1310.6289, TeX
  l.241–242). So a positive answer implies that every finitely presented simple group has `β_1^(2) = 0`.
- **Lodha's question.** The only known general lower bound for the rank of an infinite simple group is
  `d ≥ 1 + β_1^(2)` (`fp-infinite-simple-group-not-two-generated`, Attempt 2). A positive answer here would
  therefore close that route for every finitely presented simple group, not only for the families of
  `simple-groups-on-trees-with-fg-edge-groups-have-b1-zero` and
  `locally-moving-groups-have-vanishing-first-l2-betti-number`.
- **Mechanism.** Osin's proof of the known case uses the same two inputs as
  `simple-groups-on-trees-with-fg-edge-groups-have-b1-zero`:
  - a splitting over a finitely generated subgroup, here the Bieri–Strebel HNN splitting coming from the map
    onto `Z`;
  - the Peterson–Thom theorem that a finitely generated s-normal subgroup of infinite index kills
    `β_1^(2)`, followed by Minasyan–Osin.

  What is missing in general is a splitting, i.e. an action on a tree with finitely generated edge
  stabilizers, for finitely presented groups that do not map onto `Z`.

## Lesson for general BH

Finitely presented simple groups sit exactly at the boundary of this problem. They are finitely presented,
never acylindrically hyperbolic, and every known family has `β_1^(2) = 0` for structural reasons: a splitting
with a finitely generated edge group, local mobility, or a product structure. So "`β_1^(2) = 0` for all
finitely presented simple groups" is the natural conjecture that Osin's problem predicts. Any Boone–Higman
host construction producing a finitely presented simple group with a nonzero `ℓ²` cocycle would be a
counterexample to it. L²-type invariants are thus no tool for separating BH hosts.
