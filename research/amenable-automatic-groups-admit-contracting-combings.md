---
rg: 2
id: amenable-automatic-groups-admit-contracting-combings
kind: claim
title: Every amenable automatic group admits a contracting combing
distinct_from:
  contracting-combings-give-contractible-rips-complexes: that is Alonso's established theorem that contracting combings give contractible Rips complexes; this is the open claim that amenable automatic groups have such combings
  amenable-automatic-groups-have-contractible-rips-complexes: that is the affirmative answer to Zaremsky Problem 4.1; this is a combing statement that implies it through Alonso's theorem
---

**OPEN.** Every amenable automatic group `G` has a finite generating set whose word
metric admits a contracting combing in Alonso's sense (definition in
`contracting-combings-give-contractible-rips-complexes`).

With Alonso's theorem this gives
`amenable-automatic-groups-have-contractible-rips-complexes` (route
`amenable-automatic-rips-via-contracting-combings`).

## Attempts

- 2026-09-13 (lane z4-01-amen-auto-rips): an automatic structure gives a bounded
  combing with linear `φ(n) = Cn + D` (Zaremsky, arXiv:1812.10976v3, after
  Citation 6.7). The contracting condition says that stepping `⌊C/2⌋` back along one
  combing line keeps it `C`-close to a later point of another. That is hyperbolic-type
  control, and linear fellow travelling does not give it. Hyperbolic groups have
  contracting combings.
- Virtually abelian groups: no contracting combing is recorded. Zaremsky writes in
  1812.10976v3 (after Theorem 6.5) that he was then "not even sure whether `Z^n` with
  the standard word metric admits a contractible proper Vietoris–Rips complexes for
  all n". Their contractible Rips complexes in this graph come from dominated-vertex
  collapses, not combings (`linf-preserving-proper-actions-give-contractible-rips`).
  So this route may be strictly stronger than needed.
- 2026-09-16 (lane swarm-zaremsky-4-01-amenable-automat), recorded in
  `research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md`:
  - The definition had been recorded with `n <= n'`. That reading holds only for
    finite groups, and it would have made this claim false. The source says `n' <= n`,
    and the definition is now corrected.
  - Virtually abelian groups do have contracting combings for a broad class:
    `linf-lattice-groups-admit-contracting-combings`. The class is actions transitive
    on `Z^n` by signed-permutation affine maps, including non-split holonomy. The
    combing clamps the translation part coordinatewise. Plane groups containing `p3`,
    such as `p3` and `p6`, are not covered in any coordinates, and no construction
    is known for them. It is not settled which 3-dimensional trigonal and hexagonal
    groups are covered; `Z^3 ⋊ C_3` with cyclic coordinate permutation is.
  - The generating set must be chosen:
    `l1-product-word-metrics-admit-no-contracting-combing`. `Z^2` with its standard
    generators, over which it is automatic, has no contracting combing. So improving
    the combing of a given automatic structure cannot work in general.
  - No mechanism turning amenability plus automaticity into a contracting combing was
    found. The only visible general route is still the structure claim
    `amenable-automatic-groups-are-virtually-abelian`, which would also need the
    remaining virtually abelian cases.
