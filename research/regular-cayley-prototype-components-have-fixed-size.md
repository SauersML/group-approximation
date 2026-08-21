---
rg: 2
id: regular-cayley-prototype-components-have-fixed-size
kind: claim
title: Closed regular-Cayley prototype components cannot grow
distinct_from:
  finite-telescope-level-coset-orbits: that obtains growing finite orbits by changing the stabilizer through an HNN tower; this treats one regular orbit with one fixed finite menu of relative edge words.
  regular-tree-consistency-has-vanishing-spectral-gap: that gives the quantitative failure for finite tree truncations; this is the exact component classification for every group.
---

Let a group `H` act regularly on itself and let `D` be the finite set of
relative offsets appearing in all prototype occurrence-consistency edges.
The full translated consistency graph has edges

```text
g -- g d,       g in H, d in D union D^-1.                      (RCP1)
```

Its connected components are exactly the right cosets of the one fixed
subgroup `L=<D>`.  Hence a finite vertex set closed under the complete
prototype edge menu is a union of finite `L`-cosets.  A connected closed
component has size `|L|`: it is either one fixed finite size or it is
infinite.  In particular this regular-orbit construction cannot furnish
finite equality components whose sizes tend to infinity.

One may truncate an infinite component, but then some prototype edges are
missing.  On a free/regular-tree addresser the resulting consistency gap
vanishes by `regular-tree-consistency-has-vanishing-spectral-gap`.  One may
instead close the chart in a finite quotient, but choosing occurrence words
then reintroduces a quotient-section/stabilizer cocycle.  Thus the only
unexcluded Cayley version would need literal large expander subgraphs inside
one Cayley graph together with a globally exact hard local rule; ordinary
tree charts and ordinary finite-quotient closure do not supply it.

