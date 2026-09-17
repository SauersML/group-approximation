---
rg: 2
id: xl-exact-groups-admit-commuting-minimal-amenable-spaces
kind: claim
title: Every exact nonamenable group has a finite-dimensional amenable space with a commuting free minimal Z- or locally finite action (CMA)
distinct_from:
  stw40-unital-nuclear-no-trace-iff-exact: that only asks for a compact amenable G-space; CMA additionally demands a commuting free minimal action of an amenable group, which forbids proximal factors.
---

**(CMA_G).**  For every countable exact nonamenable group `G` there is a
compact metrizable space `X` with `dim X < infinity`, a topologically amenable
action of `G`, and a commuting free minimal action of `Z` or of a countable
locally finite group.

By `xl-commuting-minimal-action-gives-classifiable-witness` this implies
Problem XL for `G`.  By `xl-commuting-minimal-action-forbids-proximal-factors`
the space `X` has no nontrivial proximal `G`-factor, so it cannot be built
over a boundary.  Open; even one nonamenable `G` (for example a free group)
would give a new class of XL witnesses.
