---
rg: 2
id: fp-groups-without-free-subsemigroups-are-virtually-nilpotent
kind: claim
title: A finitely presented group without a free subsemigroup of rank two is virtually nilpotent
distinct_from:
  fp-group-of-intermediate-growth-exists: that asks for a finitely presented group of intermediate growth; this conjecture would rule one out and says more
  no-free-subsemigroups-give-fg-kernels-over-ea-quotients: that is a published finite-generation theorem for such groups; this is the full conjecture
artifacts:
  - research/artifacts/solve-fp-intermediate-growth-2026-09-13.md
---

**OPEN.** Grigorchuk's conjecture, from *Milnor's problem on the growth of groups and its
consequences* (arXiv:1111.0512, TeX l.652–658, read on MSI): "In [Grigorchuk–Pak], it is
conjectured that there are no finitely presented groups of intermediate growth. At the same
time, the author suggests even a stronger conjecture. A finitely presented group either
contains a free subsemigroup on two generators or is virtually nilpotent."

If true it refutes `fp-group-of-intermediate-growth-exists`: a group of intermediate growth
contains no free subsemigroup, and it is not virtually nilpotent, since virtually nilpotent
groups have polynomial growth (Wolf; Bass–Guivarc'h).

## Attempts

1. **Splittings and maps onto Z.** A group without free subsemigroups splits as an HNN
   extension only as `H ⋊ Z` (`non-automorphic-hnn-extensions-contain-free-subsemigroups`), and
   normal subgroups with elementary amenable quotient are finitely generated
   (`no-free-subsemigroups-give-fg-kernels-over-ea-quotients`). Neither uses finite presentation,
   so neither separates the finitely presented case.
