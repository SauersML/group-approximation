---
rg: 2
id: st-n-r-l-no-type-a-action-via-centre
kind: route
title: Central K_2 makes the rational scalars central in St_N(R_L), and pair-finite faithful actors have finite centre
target: steinberg-leavitt-resolvent-groups-have-no-type-a-action
requires:
  - leavitt-resolvent-ring-is-fp-and-contains-q
  - k2-central-in-steinberg-groups-of-leavitt-resolvent-ring
  - faithful-pair-finite-steinberg-actions-need-noncentral-k2
---

- `R_L` contains `Q` as a unital subring and has a Leavitt pair
  (`leavitt-resolvent-ring-is-fp-and-contains-q`). So it satisfies the
  hypotheses of `faithful-pair-finite-steinberg-actions-need-noncentral-k2`,
  for every `N >= 3`.
- For `N >= 5`, `K_2(N,R_L)` is central by
  `k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`.
- Item 3 of the implication node then says that no action of `St_N(R_L)` with
  finitely many orbits of two-element subsets is faithful.
