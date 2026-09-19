---
rg: 2
id: locally-torsion-subgroups-of-v-have-measured-minimal-sets
kind: claim
title: If every element of a subgroup of Thompson's group V has a power that is the identity on a neighbourhood of a minimal invariant set, that set carries an invariant probability measure
distinct_from:
  slope-principal-minimal-sets-of-nv-subgroups-carry-measures: that is the slope hypothesis in nV for all n; this is its exact n = 1 content after the torsion rigidity of slope-principal-sets-of-v-are-locally-of-finite-order, stated as a Burnside-type question about V with no slope hypothesis left.
  slope-principal-sets-of-v-are-locally-of-finite-order: that proves the torsion rigidity from slope-principality; this asks for the measure that the rigidity does not give.
  elek-free-minimal-cantor-actions-with-invariant-measures: that builds one measured free minimal action of a given group; this asks that every minimal set of a pointwise locally trivial torsion subgroup of V is measured.
artifacts:
  - research/artifacts/slope-principal-torsion-rigidity-2026-09-18.md
---

Let `G <= V` and let `Z ⊆ C` be a minimal closed `G`-invariant set such that for every
`g ∈ G` there are `q >= 1` and a clopen `W ⊇ Z` with `g^q|_W = id`. Then `Z` carries a
`G`-invariant Borel probability measure.

## Status

OPEN.

## Why this is exactly the n = 1 case of the (T)-free half

By `slope-principal-sets-of-v-are-locally-of-finite-order` (Theorem A), a slope-principal
closed invariant set of a subgroup of `V` satisfies the hypothesis above; conversely, if
`g^q` is the identity near `Z` then every fixed point of every element of `G` in `Z` has
zero slope, because a nonzero slope at a fixed point is a nonzero value of a
homomorphism to `Z^n` on a group element of finite order
(`nv-point-germ-groups-embed-in-zn-by-slope`, item 1). So for `n = 1` this claim and
`slope-principal-minimal-sets-of-nv-subgroups-carry-measures` have the same content.

## Burnside shape of a counterexample

A counterexample is a minimal `Z` with no invariant measure, so `G|_Z` is not amenable,
so not locally finite, so some finitely generated `H = ⟨g_1,…,g_k⟩ <= G` has infinite
image `H|_Z`. By the hypothesis `H|_Z` is a torsion quotient of
`Z/m_1 * … * Z/m_k`: an infinite finitely generated torsion group, acting minimally on a
Cantor set, non-amenably, with all germs at fixed points trivial, and realized as germs
of elements of `V` along `Z`. The orbit relation of such an action lies in the tail
relation of `C` with the slope as lag, and the slope sums to zero around every cycle of
every single element.

## Attempts

- 2026-09-18 (lane `e2-w2-nv-kazhdan-halves`, wave `swarm-0917`, symbolic-dynamics,
  inverter). The node was produced, not attacked; here is where the two obvious attacks
  die, from the work in
  `research/artifacts/slope-principal-torsion-rigidity-2026-09-18.md`.
  - *Local finiteness of the germ group.* The hypothesis gives one exponent per element,
    not per finitely generated subgroup, so it yields only that `H|_Z` is a torsion
    quotient of `Z/m_1 * … * Z/m_k`. Making it finite is a Burnside statement; nothing in
    the graph bounds the exponent uniformly, and `V` is not known to be free of infinite
    finitely generated torsion subgroups.
  - *AF comparison.* The orbit relation of `G` on `Z` lies in the tail relation of `C`
    with the slope as lag. The lag-zero tail relation is AF, and every AF relation on a
    Cantor set has an invariant measure, which would finish the proof; but the lag is a
    coboundary only orbit by orbit, and the height `F` on an orbit is unbounded whenever
    the minimal set is not already in `U_G`
    (`bounded-slope-at-one-point-puts-nv-minimal-set-in-u-k`). So the conjugation to a
    lag-zero relation is not available, and this is the same wall as the vanishing-error
    transport recorded on `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`.
  - *What would settle it.* Either an infinite finitely generated torsion group of germs
    of `V`-elements along a minimal set, acting non-amenably, or a uniform exponent bound
    forcing local finiteness.

## What it is not

- It is not the statement that torsion subgroups of `V` are locally finite: `G` itself
  need not be torsion, only its restriction to a neighbourhood of `Z`, one element at a
  time.
- It has no property (T) in it, and no `n >= 2` content: by Theorem B of
  `slope-principal-sets-of-v-are-locally-of-finite-order` the torsion rigidity is false
  for `n >= 2`, where a slope-principal minimal set can carry infinite-order elements
  with no periodic points in it (Brin's baker map on the natural extension
  `⋂_{k >= 0} b^k(S × C)` of an aperiodic minimal subshift `S`).

**Provenance caveat (2026-09-18).** The node
`slope-principal-sets-of-v-are-locally-of-finite-order` was demoted to OPEN at landing,
so the equivalence above rests on an attempt, not on established graph state. Theorem A,
which is the direction this node's hypothesis comes from, survived all three referee
lenses; what was refuted was Theorem B's witness set, since corrected but not re-refereed.
