---
rg: 2
id: amenable-fg-simple-groups-are-not-left-orderable-proof
kind: route
title: Witte Morris's theorem and the circle fixed-point theorem exclude one-manifold actions of amenable finitely generated simple groups
target: amenable-fg-simple-groups-are-not-left-orderable
requires:
  - amenable-left-orderable-groups-are-locally-indicable
  - amenable-infinite-simple-circle-groups-fix-a-point
---

Let `S` be finitely generated, infinite, simple and amenable.

1. **Not left-orderable.** Suppose `S` is left-orderable. By
   `amenable-left-orderable-groups-are-locally-indicable`, every nontrivial finitely
   generated subgroup of `S` maps onto `Z`. `S` is itself nontrivial and finitely
   generated, so there is a surjection `S -> Z`. Its kernel is a proper normal
   subgroup, so it is trivial and `S ≅ Z`, which is not simple. Contradiction.
2. **Actions on the line.** A homomorphism `S -> Homeo(R)` has a normal kernel, so it
   is trivial or injective. The orientation character `S -> Z/2` is trivial, since `S`
   is simple and infinite, so an injective one lands in `Homeo⁺(R)`. A countable group
   acting faithfully on `R` by orientation-preserving homeomorphisms is left-orderable:
   fix a dense sequence `x_1, x_2, ...` in `R`, and for `g != 1` let `i(g)` be the least
   `i` with `g(x_i) != x_i`. The set `P = {g != 1 : g(x_(i(g))) > x_(i(g))}` is a
   semigroup with `S = P ⊔ {1} ⊔ P^{-1}`, so `g < h` iff `g^{-1} h ∈ P` is a
   left-invariant order. By step 1 this is impossible, so every action on `R` is
   trivial.
3. **Actions on the circle.** A nontrivial action on `S^1` is faithful, as in step 2.
   By `amenable-infinite-simple-circle-groups-fix-a-point` it has a global fixed point
   `p` and restricts to a faithful action on `S^1 \ {p} ≅ R`, which step 2 excludes. So
   every action on the circle is trivial. ∎

Step 2's semigroup check: for `g, h ∈ P`, let `i = min(i(g), i(h))`. Then `gh` fixes
`x_j` for `j < i`, and `gh(x_i) > x_i`: if `i(h) = i`, `h(x_i) > x_i` and `g` is
increasing and fixes or raises `x_i`; if `i(g) = i < i(h)`, `h(x_i) = x_i` and
`g(x_i) > x_i`. So `i(gh) = i` and `gh ∈ P`.
