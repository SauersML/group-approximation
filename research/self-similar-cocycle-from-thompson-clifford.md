---
rg: 2
id: self-similar-cocycle-from-thompson-clifford
kind: route
title: The Thompson central product is the required fixed nontrivial binary cocycle
target: self-similar-central-sign-cocycle
requires:
  - thompson-clifford-central-product-tape
  - thompson-v-central-extensions-split
---

Take `Gtilde=VCl` and

```text
G=(directSum_X F_2^2) semidirect V.
```

The extension `(TCP2)` supplies the central class.  Equation `(TCP3)` is its
binary self-similarity equation in the correct category: the two child
extensions are centrally amalgamated along the same `J`, rather than placed
in a direct product whose two negative scalars would multiply to `+1`.
Restriction to either child is nontrivial because a transported Pauli pair
still has commutator `J`.  The sibling swap gives coherence, the sites
`0^n10^infinity` add one relative qubit per level, and the finite presentation
has linear-depth addressing.  The crossed-product trace keeps `J=-I` at every
depth.  These are precisely the four concrete consequences required by the
target.  The splitting theorem confirms that all holonomy lies in the
Clifford kernel, not in the bare Thompson subgroup.
