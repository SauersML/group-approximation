---
rg: 2
id: sl3z-is-incoherent
kind: claim
title: SL_3(Z) has a finitely generated subgroup that is not finitely presented
distinct_from:
  sl3z-is-coherent: that claim is the affirmative answer to Serre's question; this is its negation, the negative answer
---

`SL_3(Z)` is incoherent: some finitely generated subgroup `N <= SL_3(Z)` is
not finitely presented. This is the negative answer to Serre's question
(`zaremsky-3-04-sl3z-coherent`). When one side is established, stamp
`refuted_by:` on the other.

## Attempts

- 2026-09-13 (z3-04-sl3z-incoherent): Stallings' mechanism (a fibre product
  inside `F_2 x F_2`) is dead, because `SL_3(Z)` contains no `F_2 x F_2`; the
  obstruction and the dead route land next
  (`sl3z-products-of-infinite-subgroups-are-polycyclic`).
- Any witness `N` is Zariski dense of infinite index, since finitely
  generated subgroups that are not Zariski dense are finitely presented
  (`sl3z-non-zariski-dense-fg-subgroups-are-fp`).
- Live criterion 1: a subgroup `G` of type F with `cd G = 2`, `chi(G) != 0`
  and an epimorphism `G -> Z` with finitely generated kernel; that kernel is
  then not finitely presented (Wang-sequence Euler characteristic argument).
- Live criterion 2: a finitely generated virtually RFRS subgroup of
  cohomological dimension two with positive second L²-Betti number, which is
  incoherent by `virtually-rfrs-cd2-coherence-characterization`.
- Candidate sources, to test: thin hyperbolic subgroups of cohomological
  dimension two with positive Euler characteristic (e.g. torsion-free C'(1/6)
  groups with at least as many relators as generators, which are cubulated,
  hence virtually special); free-by-free thin subgroups. Where each dies is
  recorded in `research/artifacts/zp-sl3z-coherence-2026-09-13*.md` as the
  analysis lands.
