---
rg: 2
id: fpbs-positive-gradient-torsion-group-cheap-action
kind: claim
title: Some finitely generated residually finite torsion group of positive rank gradient has a free action cheaper than one plus its rank gradient
distinct_from:
  fpbs-burnside-upper-cost-one: that asks for upper cost one for bounded-exponent Burnside groups, which have no Farber chains; this asks for a cheap action of a residually finite torsion group, necessarily of unbounded exponent, whose profinite actions are already expensive.
  fpbs-kazhdan-positive-rank-gradient: that has the cheap side from Hutchcroft-Pete and lacks the expensive side; this has the expensive side unconditionally, by fpbs-power-deficiency-torsion-profinite-cost-gap, and lacks the cheap side.
  fpbs-normal-finite-cost-rankgradient-counterexample-reduction: that is a conditional implication whose cheap side needs an infinite finite-cost normal subgroup; this is an unconditional cheap-action target for a class where the expensive side is proved.
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

**OPEN.** There is a finitely generated residually finite torsion group `Q`
with `RG(Q) = inf_U (d(U)-1)/[Q:U] > 0`, together with a free p.m.p. action of
`Q` of cost strictly less than `1 + RG(Q)`.

The class is nonempty: `fpbs-power-deficiency-torsion-profinite-cost-gap`
gives `RG(Gamma') >= 1 - 1/(p(p-1))`.

## Attempts

* **Known cheap-action theorems** (swarm-0917 w5 heretic, 2026-09-17). Where each dies:
- Bounded-centralizer certificates:
  `fpbs-farber-excludes-bounded-exponent-certificates`.
- Hutchcroft--Pete: no (T).
- Theorem S: `RG > 0` is multiplicative, so there are no isomorphic
  finite-index subgroups of unequal index.

Fixed price predicts that this claim is false.
