---
rg: 2
id: periodic-linf-proximity-complexes-are-contractible
kind: claim
title: The l-infinity proximity flag complex of a lattice-periodic discrete subset of R^n is contractible at every scale at least 4
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for Z^n in the l^1 metric; this is the l^infinity metric on any finite union of cosets of a lattice, where a dominated-vertex collapse works at every scale c >= 4
  contractible-rips-groups-closed-under-direct-products: that computes Rips complexes of products with the l^infinity generating set; this is a statement about subsets of R^n that need not be products, such as orbits of crystallographic groups with glide reflections
---

**ESTABLISHED** (route `periodic-linf-proximity-complexes-are-contractible-proof`).

Let `e_1, ..., e_n` be a basis of `R^n`, write `x = Σ x_i e_i`, and put
`‖x‖_∞ = max_i |x_i|`. Let `O ⊆ R^n` be a nonempty discrete set with `O + e_i = O`
for every `i`, that is, a finite union of cosets of `Λ = ⊕ Z e_i` (finite because
`O` is discrete and `Λ`-invariant). For `c >= 4` let `K_c(O)` be the flag
complex of the graph on `O` in which `u ≠ w` are adjacent iff `‖u − w‖_∞ <= c`.
Then `K_c(O)` is contractible.

`O` need not be a lattice or a product: for example `O` can be the orbit of a
point under a crystallographic group whose linear parts permute `±e_i` and
whose translation parts are not in `Λ` (glide reflections, screw motions).
