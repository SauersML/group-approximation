---
rg: 2
id: binary-four-address-single-flip-census-proof
kind: route
title: Solve single invisible flips on every quotient partition, then decide each minimal failing table group exactly
target: binary-four-address-single-flip-balance-census
requires:
  - three-address-binary-injective-rules-are-balanced
  - amenable-groups-satisfy-the-garden-of-eden-theorem
  - bijective-ca-preserve-uniform-bernoulli-measure
artifacts:
  - research/artifacts/gk3-four-address-balance-census-2026-09-14.md
---

Sections 1–6 of the artifact. Code and data are in `experiments/gottschalk-four-address-balance/`.

1. **Reductions.**
   - Translate so that `1 in M`, and restrict to `H = <M>`: injectivity over `G` holds iff it holds over `H`.
   - Rules ignoring a coordinate fall under `three-address-binary-injective-rules-are-balanced`.
   - Constants must map to distinct constants.
   - If `H` is amenable, an injective automaton is pre-injective, hence surjective by
     `amenable-groups-satisfy-the-garden-of-eden-theorem`. So it is bijective, and by
     `bijective-ca-preserve-uniform-bernoulli-measure` its rule is balanced.
2. **Single flips.** A flip at `h` is invisible iff the blind contexts of the four coordinates agree on the sites
   `h m_i^-1 m_j`. Their coincidences are exactly the quotient partition of the twelve ordered pairs.
   - Enumerate the 1124 admissible partitions, and solve the constraint problem for each of the 394 rule classes
     that remain (`flip1.py`, MSI job 781776).
   - Coarsening only adds constraints, so the failing partitions are determined by their minimal elements.
3. **Table groups.** Every group whose memory has no invisible flip realizes a coarsening of some minimal failing
   `P`, so its memory group is a quotient of `G_P`. Each distinct `G_P` is decided exactly (`analyze2.py`, `gp.py`):
   - Tietze elimination and Nielsen moves;
   - free products and graph products of cyclic groups, with their normal forms and amenability criteria;
   - cyclic-by-cyclic groups;
   - finite groups by complete coset tables in two strategies.

   Undecided groups count as not excluded.
4. **Exclusion.** A rule is excluded when every minimal failing partition has an amenable table group or collapses
   the memory. Then any realization either has an invisible flip or an amenable memory group, and step 1 applies.
5. **Controls.**
   - `control1.py` (job 791356) checks the flip census by brute force on nine finite groups: 864 of 864 agree.
   - `control2.py` (job 792968) re-derives the triage: all relators vanish (826 of 826), the flags agree, and the 36
     finite orders are re-derived.
