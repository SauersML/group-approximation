---
rg: 2
id: contractible-rips-complex-gives-finite-classifying-space-proof
kind: route
title: Free cocompact action of a torsion-free group on its contractible Rips complex
target: contractible-rips-complex-gives-finite-classifying-space
requires: []
---

Let `X = R_r(G,S)`: vertex set `G`, a finite `σ ⊆ G` is a simplex iff
`d_S(x,y) ≤ r` for all `x, y ∈ σ`. `G` acts by left multiplication, which
preserves `d_S`, so it acts simplicially.

1. **Free on simplices.** Suppose `gσ = σ` for a simplex `σ`. Then `g`
   permutes the finite vertex set of `σ`, so `g^m` fixes every vertex for
   `m = |σ|!`. The action on vertices is free, so `g^m = 1`, and `g = 1`
   because `G` is torsion-free. Every setwise stabilizer of a simplex is
   trivial.
2. **Cocompact, finite-dimensional.** Translate a simplex so that it contains
   the vertex `1`. It is then a subset of the ball `B_S(r)`. So there are
   finitely many orbits of simplices, and `dim X ≤ |B_S(r)| − 1`. `X` is
   locally finite.
3. **Quotient.** A free simplicial action with trivial setwise stabilizers is
   properly discontinuous on the CW complex `|X|`, so `|X| → |X|/G` is a
   covering map and `|X|/G` is a CW complex with one cell per orbit of
   simplices, hence finite. `|X|` is contractible, so it is the universal cover,
   `π_1(|X|/G) ≅ G` and `π_k(|X|/G) = 0` for `k ≥ 2`. So `|X|/G` is a finite
   `K(G,1)`, and `G` is of type F.

For the remark in Zaremsky Problem 4.6: a group of finite cohomological
dimension is torsion-free, because a nontrivial finite cyclic subgroup has
infinite cohomological dimension and cd is monotone under passing to
subgroups.
