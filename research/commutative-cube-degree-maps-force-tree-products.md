---
rg: 2
id: commutative-cube-degree-maps-force-tree-products
kind: claim
title: The pointed-cube category of a CAT(0) cube complex admits a degree map with unique factorization into a commutative monoid exactly when the complex is a product of trees
distinct_from:
  cocompact-tree-product-lattices-lie-in-type-a-class: that uses the commutative (cube k-graph) degree on products of trees; this shows no other cube complex has one.
---

**ESTABLISHED** (lane proof, elementary; uses only standard facts on CAT(0) cube
complexes: consecutive edges dual to crossing hyperplanes span a square, geodesics
between two vertices are related by square flips, Helly for half-spaces, and the
Caprace--Sageev product decomposition; not independently reviewed; no priority
claimed).

**Setting.** `X` is a locally finite, finite-dimensional CAT(0) cube complex. `G` acts
on it freely on vertices and cocompactly. `C_X` is the pointed-cube category of
`cubulated-groups-act-by-bisections-of-a-pointed-cube-category`: morphisms are
`G`-classes of geodesic segments with an incoming cube, and units are identities.

**Theorem.** Let `P` be a cancellative commutative monoid with `P^* = 0`. There is a
functor `d: C_X → P` with `d^{-1}(0) = C_X^*` and Li's unique factorization (UFP*)
exactly when the hyperplanes of `X` split into classes `𝓗_1, …, 𝓗_m` such that:
- two hyperplanes in different classes always cross;
- two hyperplanes in the same class never cross.
Equivalently, `X ≅ T_1 × … × T_m` with each `T_j` a tree. Then `d` may be taken to be
"number of hyperplanes of each class crossed", with values in `N^m`: this is the cube
`m`-graph.

**Proof.**
1. **Atoms have atomic degrees.** An atom of `C_X` crosses one hyperplane. If
   `d(a) = p + q` with `p, q ≠ 0`, (UFP*) would factor `a`. So `d(a)` is an atom of `P`,
   its *colour*.
2. **Squares.** Consecutive crossings of crossing hyperplanes `H_1, H_2` at a vertex
   span a square. The two-step morphism `c` then has two atom factorizations with
   different first atoms. If both first atoms had the same colour, (UFP*) uniqueness
   (units are trivial) would identify them. So they have **different colours**.
   Commutativity then gives `{col(H_1), col(H_2)}` equal before and after the flip, so
   each hyperplane keeps its colour under square flips. Hence inside any morphism `m`,
   the colour `col_m(H)` of each crossed hyperplane `H` is well defined.
3. **Nested steps.** Suppose a geodesic crosses `H_1` and then, consecutively, `H_2`,
   with `H_1, H_2` not crossing. Then `H_2` is not adjacent to the first vertex, so every
   factorization of the two-step morphism starts by crossing `H_1`. If
   `col(H_1) ≠ col(H_2)`, then since `P` is commutative, `d(c) = col(H_2) + col(H_1)`.
   (UFP*) would then give a factorization starting with degree `col(H_2)`, which is
   impossible. So they have the **same colour**.
4. **Inside one morphism.** Let `H, H' ∈ H(y,z)`.
   - If they cross, some linear extension of the separation order makes them
     consecutive, and step 2 gives different colours.
   - If not, pass through a maximal chain of covering relations between them. Each
     step can be made consecutive, and step 3 makes all colours equal.
   So within `H(y,z)`, "same colour ⇔ not crossing".
5. **Globally.** Define `H ∼ H'` iff `H = H'` or `H, H'` do not cross.
   - **Any two hyperplanes lie in one morphism.** For any two hyperplanes, and for any
     three of which two do not cross the third, Helly for half-spaces gives vertices
     `y, z` separated by all of them. (For each disjoint pair, one diagonal pair of
     quadrants is nonempty, and these choices are compatible.) The segment from `y` to
     `z`, with the trivial incoming cube `{y}`, is a morphism of `C_X`.
   - **Transitivity.** Suppose `H ∼ H' ∼ H''` but `H` and `H''` cross. In one such
     morphism, step 4 makes all three the same colour, while `H` and `H''` must differ.
     This is a contradiction.
   So `∼` is an equivalence relation. Its classes pairwise cross, and each class has no
   crossing pairs. By Caprace--Sageev's product decomposition, `X` is the product of the
   classes' restriction quotients, and each is a CAT(0) cube complex with no crossing
   hyperplanes, i.e. a tree.
6. **Converse.** For `X = ∏ T_j`, the class-count degree has (UFP*): paths reorder
   freely across factors and are rigid within each factor.

**Consequence for Li's machinery.** Li's sufficient multiplicity lemma for his condition
(`t < d`) (arXiv:2110.04505v2, `lem:deg--t<d`, read at source) and the power-and-phase
trick of `tree-lattice-kgraph-power-phase-proof` both need an additive (commutative or
Ore) degree. So on pointed-cube codings they reach exactly products of trees. This
recovers `cocompact-tree-product-lattices-lie-in-type-a-class`, and a non-product
cubulated group needs a different coding. `raag-cube-codings-fail-li-multiplicity-at-every-power`
shows that the non-commutative trace degree fails too.

## Lesson for general BH

Commutative, and hence "powerable", gradings exist on a cube category only when all
directions commute globally, i.e. for products of trees. The power trick that supplies
Li's loop-richness is therefore special to products. Any rank-≥2 host coded by
geodesics with flats that do not split needs a different source of loops.
