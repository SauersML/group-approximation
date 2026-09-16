---
rg: 2
id: kropholler-question-via-zero-divisor-split
kind: route
title: Kropholler's question follows from its zero-divisor half and its domain half
target: amenable-groups-of-finite-cd-are-virtually-solvable
requires:
  - amenable-finite-cd-integral-group-rings-are-domains
  - amenable-finite-cd-domain-groups-are-virtually-solvable
artifacts:
  - research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md
---

## Why sufficient

Let `G` be amenable with `cd_Z G < ∞`.

1. `amenable-finite-cd-integral-group-rings-are-domains` makes `Z[G]` a domain.
2. So `G` satisfies every hypothesis of `amenable-finite-cd-domain-groups-are-virtually-solvable`,
   which makes `G` virtually solvable.

That is the target. ∎ (This is artifact Lemma 1.1.)

## Converse

The target implies both prerequisites (artifact Lemma 1.3).

- It implies the second prerequisite directly.
- It implies the first because a virtually solvable group of finite cd is torsion-free and
  elementary amenable, so its complex group ring is a domain
  (`elementary-amenable-torsion-free-strong-atiyah`).

The split is therefore an equivalence. The converse is not recorded as routes, which keeps the graph
acyclic. The split separates the ring-theoretic input (a special case of Kaplansky's conjecture)
from the group-theoretic one, where Degrijse's Theorems A and B live and where the known cases are
(dimension at most 2 unconditionally, and several cases in dimension 3).
