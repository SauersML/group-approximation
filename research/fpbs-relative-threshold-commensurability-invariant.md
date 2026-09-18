---
rg: 2
id: fpbs-relative-threshold-commensurability-invariant
kind: claim
title: Relative percolation thresholds are unchanged under finite-index passage, so relative gaps need an infinite-index subgroup
distinct_from:
  fpbs-relative-gap-along-any-subgroup-separates: that proves a relative gap along any infinite subgroup separates the thresholds; this shows the relative threshold only sees a subgroup up to finite index, so every such route needs an infinite subgroup of infinite index and dies on groups with none.
  fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups: that kills soft arguments on groups with a finitely generated normal subgroup and on Kazhdan groups; this kills relative-gap arguments on groups whose infinite subgroups all have finite index, a class disjoint from the first.
---

**ESTABLISHED.** Let `G = Cay(Gamma,S)` for a finitely generated group `Gamma`,
and let `I <= J <= Gamma` with `[J:I] < infinity`. Then

```text
p_c(I;G) = p_c(J;G).
```

Here `p_c(H;G)` is Hutchcroft--Pan's relative threshold for the existence of a
cluster that meets `H` in infinitely many vertices. In particular,
`p_c(I;G) = p_c(G)` for every finite-index subgroup `I` of `Gamma`.

**Obstruction corollary.** Suppose every infinite subgroup of `Gamma` has
finite index. Then on every Cayley graph of `Gamma`, `p_c(I;G) = p_c(G)` for
every infinite `I <= Gamma`, so condition 1 of
`fpbs-relative-gap-along-any-subgroup-separates` fails for every admissible
`I`.

- **The class.** The hypothesis holds for Ol'shanskii's torsion Tarski
  monsters, whose proper subgroups are all finite cyclic
  (`fpbs-monster-groups-have-only-finite-amenable-subgroups`), and for any group
  whose proper subgroups are all finite. It fails for torsion-free Tarski
  monsters, whose proper subgroups are infinite cyclic of infinite index. For
  those the relative route survives this obstruction, but a relative gap along
  a cyclic subgroup is not known.
- **The invariant.** The obstruction is the absence of an infinite subgroup of
  infinite index.
- **Where it applies.** Every route to `p_c < p_u` that goes through a relative
  gap along some subgroup dies on these groups at the step "choose `I`". This
  covers relative susceptibility bounds, relative Burton--Keane arguments and
  every fibre-bubble variant built on
  `fpbs-relative-gap-along-any-subgroup-separates`.

So for a single monster the Benjamini--Schramm gap has to be proved without
any relative threshold, and a residual-class route must treat single monsters
separately from products such as `T x T'`, which do have infinite normal
subgroups of infinite index.

DERIVATION
fpbs-relative-threshold-commensurability-invariant-proof
