---
rg: 2
id: surjunctivity-is-a-commensurability-invariant
kind: claim
title: Surjunctivity passes to finite-index overgroups and is a commensurability invariant
distinct_from:
  surjunctivity-passes-to-subgroups: that is heredity to subgroups; this adds the finite-index overgroup direction, through Curtis-Hedlund-Lyndon over the subgroup with a product alphabet, which makes surjunctivity a commensurability invariant.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

If `H <= G` has finite index and `H` is surjunctive, then `G` is surjunctive. With
`surjunctivity-passes-to-subgroups` this gives: groups with isomorphic finite-index subgroups are
either both surjunctive or both not.

**Proof idea.** Choose right coset representatives `r_1, ..., r_n`. The map
`x -> (h -> (x(h r_i))_i)` identifies `A^G` with `(A^n)^H` and intertwines the left `H`-shifts.
Curtis–Hedlund–Lyndon turns an injective automaton over `G` into an injective automaton over `H` with the
finite alphabet `A^n`. The full proof is Section 1 of the artifact.

The index must be finite: with an infinite fibre alphabet, shifting the alphabet coordinates gives an
injective map that is not onto, over every group (Remark A.1).
