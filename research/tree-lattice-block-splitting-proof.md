---
rg: 2
id: tree-lattice-block-splitting-proof
kind: route
title: The kernel of a discrete sub-product is cocompact on the complement, its normalizer there is discrete, and faithfulness makes the two kernels commute and intersect trivially
target: tree-lattices-split-into-irreducible-blocks
requires: [product-of-trees-faithful-factor-pbh-via-bass-serre-induction, discrete-factor-tree-lattice-splitting-proof, boone-higman-type-a-class-closed-under-finite-extensions, product-of-two-trees-lattices-satisfy-permutational-boone-higman, bs-class-with-faithful-member-lies-in-type-a-class]
---

Notation as in the target. This repeats Steps 1–3 of
`discrete-factor-tree-lattice-splitting-proof` with the tree `T_i` replaced by
the sub-product `X_I`.

**Minimality.** Let `S ⊊ T_i` be a `pr_i(Γ_0)`-invariant subtree. Finitely many
vertex orbits put every vertex within distance `R` of `S`. For a vertex `u ∉ S`
with projection `p` to `S`, leaflessness gives a ray from `u` leaving `p`
forever, whose points are at unbounded distance from `S`. So no such `S`
exists.

**Step 1.** A subgroup of `Aut(X_I)` is discrete iff its vertex stabilizers are
finite. Let `H` be the `Γ_0`-stabilizer of a vertex of `X_I`; then `H / K_I` is
finite. By Lemma P (P1) of `product-of-trees-faithful-factor-pbh-via-bass-serre-induction`,
applied one factor of `I` at a time, `H` and hence `K_I` act on `X_(I^c)` with
finite stabilizers and finitely many vertex orbits. By (P2), `K_I` is finitely
presented. It is faithful on `X_(I^c)`, because an element trivial there and on
`X_I` is trivial.

**Step 2.** Let `W` be the stabilizer of a vertex `x` of `X_(I^c)` in the closure
of `pr_(I^c)(Γ_0)` in `Aut(X_(I^c))`; it is compact and normalizes the discrete,
finitely generated group `D = pr_(I^c)(K_I)`. Orbits of the generators of `D`
under conjugation by `W` are compact and discrete, hence finite, so an open
finite-index `W' <= W` centralizes `D`. Each `u ∈ W'` fixes the orbit `D x`
pointwise, and this orbit is coarsely dense in `X_(I^c)`, so its projection to
every `T_j` (`j ∈ I^c`) is coarsely dense. In a leafless tree the convex hull of a
coarsely dense vertex set is everything: a vertex lies on a bi-infinite line, and
the geodesic between orbit points near the far ends of that line passes through
it. So `u` is trivial and `W` is finite. Thus `pr_(I^c)(Γ_0)` is discrete, and
by Step 1 with `I` and `I^c` exchanged, `K_(I^c)` is a faithful cocompact
lattice on `X_I`. Also `[pr_(I^c)(Γ_0) : D]` is finite, since both act on
`X_(I^c)` with finite stabilizers and `D` has finitely many orbits.

**Step 3.** Let `Γ_1 = pr_(I^c)^(-1)(D)`, of finite index in `Γ_0`. For
`γ ∈ Γ_1` choose `k ∈ K_I` with `pr_(I^c)(k) = pr_(I^c)(γ)`; then
`k^(-1)γ ∈ K_(I^c)`. So `Γ_1 = K_I K_(I^c)`. Both are normal in `Γ_0`, and
`K_I ∩ K_(I^c)` acts trivially on `X`, so it is trivial. Hence
`[K_I, K_(I^c)] = 1` and `Γ_1 ≅ K_I x K_(I^c)`. This is item 1.

**Item 2.** Induct on `n`: if `Γ` is not irreducible, split by item 1 and
decompose each factor. The factors are faithful cocompact lattices on products
of leafless trees, so the induction applies. Finite-index subgroups of the pieces
multiply to a finite-index subgroup of `Γ_0`.

**Item 3.** `B_A` is closed under finite direct products and finite-index
overgroups (items 1 and 2 of `boone-higman-type-a-class-closed-under-finite-extensions`).
A block on one tree acts on it with finite stabilizers and finitely many orbits,
so it is virtually free (virtually `Z` on a line), and these lie in `B_A`
(`bs-class-with-faithful-member-lies-in-type-a-class`, the cases `G = F_k` and `G = Z^n`).
