---
rg: 2
id: nonamenable-almost-malnormal-subgroups-are-not-co-amenable
kind: claim
title: A proper nonamenable subgroup whose intersections with its other conjugates are amenable is not co-amenable, and neither is any of its subgroups
distinct_from:
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: that excludes every proper subgroup of an infinite simple Kazhdan ambient group using property (T) of the ambient; this puts no hypothesis on the ambient and uses only the nonamenability of the subgroup and amenable self-intersections.
  thompson-t-orbits-carry-no-invariant-means: that shows finite point sets of the circle are uniformly non-invariant under T, so point stabilizers are not co-amenable; this is a general statement about almost malnormal nonamenable subgroups of any countable group.
  fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap: that turns non-co-amenability into a Schreier spectral gap; this proves non-co-amenability for a structural class of subgroups.
  kesten-amenable-stabilizer-uniform-gap: that is the Kesten gap on coset spaces of amenable subgroups, used as the input here; this transfers it to coset spaces of a nonamenable almost malnormal subgroup.
---

**ESTABLISHED.** Let `G` be a countable group and `H < G` a proper subgroup such that
- `H` is nonamenable, and
- `H ∩ gHg^{-1}` is amenable for every `g ∈ G \ H` (for instance finite: `H` almost malnormal).

Then `ℓ²(G/H)` has no almost invariant unit vectors. Quantitatively: there are a finite set
`S ⊂ H` and `κ > 0` such that for every `g ∈ G \ H` and every unit `ξ ∈ ℓ²(G/H)`,

```text
max( max_{s in S} ||s ξ - ξ|| , ||g ξ - ξ|| )  >=  c(κ, |S|) > 0.          (AM1)
```

Consequently `H` is not co-amenable in `G`, and no subgroup `K ≤ H`, and no subgroup of any
conjugate `tHt^{-1}`, is co-amenable in `G`.

Mechanism: every point of `G/H` other than the base coset has an amenable stabilizer in `H`, so the
Kesten gap of `H` confines almost invariant vectors to the base point `δ_H`, and one element outside
`H` moves `δ_H` by `√2`.

Route: `nonamenable-almost-malnormal-subgroups-are-not-co-amenable-proof`.
