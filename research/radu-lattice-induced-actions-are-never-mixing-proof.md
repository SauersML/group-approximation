---
rg: 2
id: radu-lattice-induced-actions-are-never-mixing-proof
kind: route
title: Read the vertical local action off the square relations, locate the horizontal kernel in the vertical factor, and apply the induced-mixing criterion
target: radu-lattice-induced-actions-are-never-mixing
requires:
  - induced-lattice-action-mixing-forces-c0-homogeneous-space
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-horizontal-projection-kills-delta-squared
---

# Proof

`Γ_R` acts simply transitively on the vertices of `T_h × T_v` without swapping the
factors, so `Γ_R <= Aut(T_h) × Aut(T_v)`, and `p_h`, `p_v` denote the projections.

**Part 1.** The neighbours of `o = A` in `T_v` are `xA, yA, zA`. The relations of
`(RE1)`, with their rotations and all letters involutions, give

```text
ax = xa,  ay = ya,  az = zb,   bx = xb,  by = yc,  bz = za,   cx = zc,  cy = yb,  cz = xc.
```

For `h ∈ {a,b,c}` and `v ∈ {x,y,z}` with `hv = v'h'` and `h' ∈ A`, the element `h`
maps `vA` to `hvA = v'h'A = v'A`. So `a` and `b` fix the three neighbours, and `c`
swaps `xA` and `zA` and fixes `yA`. The stabilizer of `o` in `Γ_R` is `A`, and
`H_v(o)` is open, so `p_v(Γ_R) ∩ H_v(o) = p_v(A)` is dense in `H_v(o)`. Its action on
the three edges at `o` has finite image, so `H_v(o)` acts there as `<(xA zA)>`.
`Γ_R` is transitive on vertices, so the same holds at every vertex. For a
finite-index subgroup `Γ' <= Γ_R`, a closed subgroup of `Aut(T_v)` in which
`p_v(Γ')` is dense is the closure of `p_v(Γ')`. That closure lies in `H_v`, so its
local action at each vertex is a subgroup of `<(xA zA)>` and is intransitive.
`Aut(T_3)^+` acts on the three edges at each vertex as `S_3`. Part 1 follows.

**Part 2.** By `radu-horizontal-projection-kills-delta-squared`, `(xz)^2 ∈ Λ_v`. `V`
acts simply transitively on the vertices of the 3-regular tree `{root} × T_v`, each
generator moving the base vertex to a different neighbour, so
`V = C_2 * C_2 * C_2` and `(xz)^2` has infinite order. An element acting trivially
on `T_h` lies in `{1} × Aut(T_v)`, and it lies in `{1} × H_v` because its second
coordinate is in `p_v(Γ_R)`. For `γ ∈ Γ_R` and `n = (1, n_2) ∈ Λ_v`,
`γnγ^(-1) = (1, p_v(γ) n_2 p_v(γ)^(-1))`, so `p_v(Λ_v)` is normalized by `p_v(Γ_R)`.
The normalizer of a closed subgroup is closed, and `{h : hNh^(-1) ⊆ N}` contains the
closure of any group normalizing `N`, with `h^(-1)` as well. So `p_v(Λ_v)` is normal
in `H_v`, and `Λ_v = {1} × p_v(Λ_v)` commutes with `H_h`. Hence `Λ_v` is normal in
`H_h × H_v`.

**Part 3.** Since `Γ_R <= L`, `p_h(Γ_R) <= G_1` and `p_v(Γ_R) <= G_2`, so `H_v <= G_2`.
`G_1` contains `p_h(Γ_R)`, which is transitive on the vertices of the infinite tree
`T_h`, so `G_1` is non-compact. `L` is non-discrete, so `Γ_R ≠ L`.

* *`G_2 ≠ H_v`.* The map `q : L/Γ_R → G_2/H_v`, `(g_1, g_2)Γ_R ↦ g_2 H_v`, is well
  defined because `p_v(Γ_R) <= H_v`. It is `G_1`-invariant and `G_2`-equivariant. The
  push-forward `ν` of the invariant probability measure is a `G_2`-invariant
  probability measure on the homogeneous space `G_2/H_v`. Its support is closed,
  nonempty and invariant, so it is everything. `G_2/H_v` is Hausdorff with at least
  two points, so it has disjoint nonempty open sets `U, U'`, and then
  `0 < ν(U) < 1`. The function `1_U ∘ q − ν(U)` is a nonzero `G_1`-invariant vector
  in `L^2_0(L/Γ_R)`. This contradicts the first consequence in Part 2 of
  `induced-lattice-action-mixing-forces-c0-homogeneous-space` if `Λ ↷ L ×_(Γ_R) Z` is
  mixing.
* *`G_2 = H_v`.* Then `L = G_1 × H_v`. By Part 2 of this proof, `Λ_v` is normalized by
  `H_v`, and it commutes with `G_1`. So `Λ_v` is an infinite subgroup of `Γ_R` that is
  normal in `L`, contradicting the second consequence in Part 2 of the criterion.

In both cases `Λ ↷ L ×_(Γ_R) Z` is not mixing. ∎

**Model test.** The criterion is not vacuous: for lattices `Γ` with dense projections
in `Aut(T_p)^+ × Aut(T_q)^+`, `ker p_i = 1` by Burger–Mozes (a discrete normal
subgroup of a locally quasiprimitive non-discrete closed group lies in its
quasi-center, Burger–Mozes, *Groups acting on trees*, Publ. IHES 92, Proposition
1.2.1(3), and Proposition 3.1.2(1) gives `QZ = e` when the group is locally
`∞`-transitive). There, `tree-product-lattice-nonsofic-gives-mixing-nonsofic-action`
does give mixing. Radu's lattice fails because its vertical closure is not locally
quasiprimitive.
