---
rg: 2
id: symmetric-operad-groups-full-cantor-proof
kind: route
title: Refine every local piece to a leaf, pull the common refinement of the images back leaf by leaf, and read the assembled map as one fraction; clopen transitivity is confluence of expansions in the color monoid
target: fp-symmetric-operad-groups-lie-in-the-permutational-class
requires:
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
  - permutational-boone-higman-iff-full-cantor-hosts
  - twisted-brin-thompson-finite-presentation-criterion
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target. Morphisms are Thumann's (arXiv:1409.1085) morphisms of the category of
operations of `𝒪`.
- In the symmetric case a morphism `ψ : y → x` is a permutation of `y` followed by a tensor product
  `⊗_i ψ_i` with `ψ_i : y_i → (x_i)`, one component for each entry `i` of `x`.
- Transformations (permutations and degree-1 operations) are among the morphisms.
- Cancellativity: `b∘ψ = b∘ψ'` implies `ψ = ψ'`, and symmetrically on the right.
- Calculus of fractions (Ore): for `b_1 : x_1 → X` and `b_2 : x_2 → X` there are `ψ_1, ψ_2` with
  `b_1∘ψ_1 = b_2∘ψ_2`.
- Every element of `Γ` is a fraction `a∘b^{-1}` with `a, b : x → X`.

**Step 1. The boundary is a Cantor space and `Γ` acts on it.**
- **The index category.** Its objects are expansions, and its arrows `b∘ψ → b` are refinements.
  The arrow is unique by left cancellation, and any two objects have a common refinement by Ore.
  So it is a directed preorder.
- **Leaf maps.** A leaf `j` of `y` lies over the entry `i` of `x` whose component `ψ_i` contains it.
  These maps compose and are onto, since there are no arity-0 operations.
- **Topology.** `∂X` is the inverse limit, compact and totally disconnected. It is metrizable
  because there are countably many operations. It is nonempty, as a limit of nonempty finite sets.
  It has no isolated points: by (N), every leaf of any color is split in two by a further
  refinement.
- **Cylinders.** `∂_b(i)` is the set of points whose `b`-coordinate is `i`. Cylinders form a basis.
  By compactness, every clopen set is a finite union of cylinders, and then (Ore) a union of
  cylinders of a single expansion.
- **The action.** Let `γ = a∘b^{-1}`. The expansions `b∘ρ` are cofinal (Ore again), and `γ` sends the
  point with `b∘ρ`-coordinate `l` to the point with `a∘ρ`-coordinate `l`. This is compatible and
  bijective, and it maps cylinders to cylinders. It does not depend on the fraction chosen, since
  `a∘b^{-1} = (a∘ρ)∘(b∘ρ)^{-1}`, and it is a homomorphism.
- **Locality (Loc).** Suppose `ψ, ψ' : y → x` have the same component over the entry `i`. Then for
  `j` over `i` the cylinders `∂_{b∘ψ}(j)` and `∂_{b∘ψ'}(j)` coincide.
  - Let `ψ̃` be `ψ_i` over `i` and the identity elsewhere. Then `b∘ψ = b∘ψ̃∘ρ`, where `ρ` is the
    identity on the leaves over `i`.
  - A leaf that is not expanded keeps its cylinder, so `∂_{b∘ψ}(j) = ∂_{b∘ψ̃}(j)`.
  - The same holds for `ψ'`.
  - Applied to `ψ∘ρ` and `ψ'∘ρ`, the same holds at every finer level.

**Step 2. `Γ̄` is full.**
1. **Pieces.** Let `f` be a homeomorphism that agrees locally with elements of `Γ̄`. By
   compactness and Step 1, there are a finite clopen partition `∂X = ⊔_k U_k` and elements
   `γ_k = a_k∘b_k^{-1}` with `f = γ_k` on `U_k`.
2. **One source expansion.** By Ore, choose an expansion `c`, with `c = b_k∘ψ_k` for every `k`,
   whose cylinders refine every `U_k`. Put `a'_k = a_k∘ψ_k`, so that `γ_k = a'_k∘c^{-1}`.
   - For each leaf `i` of `c`, let `k(i)` be the index with `∂_c(i) ⊆ U_{k(i)}`.
   - `f` maps `∂_c(i)` onto the cylinder `∂_{a'_{k(i)}}(i)`.
   - Since `f` is a bijection, these image cylinders partition `∂X`.
3. **One target expansion.** By Ore, choose `e` with `e = a'_k∘χ_k` for every `k`.
   - Each `e`-cylinder lies inside exactly one image cylinder `∂_{a'_{k(i)}}(i)`.
   - Let `y_i` be the set of `e`-leaves inside it. It is exactly the set of leaves over `i` in the
     component `(χ_{k(i)})_i`.
   - The sets `y_i` partition the leaves of `e`.
4. **The pulled-back expansion.** Let `ω = ⊗_i (χ_{k(i)})_i`, with its source ordered as the leaves
   of `e`. This is a morphism because `𝒪` is symmetric. Each leaf of `ω` carries the color of the
   corresponding leaf of `e`. Put `d = c∘ω`, an expansion with the same source as `e`.
5. **`f = e∘d^{-1}`.** Fix `i`, write `k = k(i)`, and take `j ∈ y_i`, a refinement `ρ`, and a leaf
   `l` over `j`.
   - `f` agrees with `γ_k = (a'_k∘ω)∘d^{-1}` on `∂_c(i)`. So it maps `∂_{d∘ρ}(l)` onto
     `∂_{a'_k∘ω∘ρ}(l)`.
   - `e∘d^{-1}` maps `∂_{d∘ρ}(l)` onto `∂_{e∘ρ}(l) = ∂_{a'_k∘χ_k∘ρ}(l)`.
   - `ω∘ρ` and `χ_k∘ρ` have the same component over `i`, so by (Loc) the two target cylinders
     coincide.
   - Two homeomorphisms that agree on a basis of cylinders shrinking to points are equal. So
     `f = e∘d^{-1}` on `∂_c(i)` for every `i`, and `f ∈ Γ̄`. ∎

**Step 3. Classes and clopen transitivity.**
1. **Confluence.** Write `m →* m'` if some morphism with target a tuple of colors `m` has source
   colors `m'`.
   - By Ore, any `m_1, m_2` with `m →* m_1` and `m →* m_2` have a common `m*`.
   - So "having a common `→*`-descendant" is an equivalence relation.
   - It is additive and contains the defining relations, so it is exactly equality in `M(𝒪)`.
2. **Well-defined classes.** If two expansions partition `U` by cylinders, their common refinement
   partitions `U` by leaves over either family. Its color multiset is a `→*`-descendant of both,
   so `[U]` is well defined.
3. **Local maps preserve classes.**
   - Classes are additive over disjoint unions: refine both parts by one expansion.
   - A `Γ̄`-local homeomorphism `U → W` is given on each cylinder `∂_c(i)` of a fine enough
     partition of `U` by one fraction `a∘b^{-1}`.
   - After refining `c` and `b` to a common `c'`, that fraction maps the `c'`-cylinders over `i`
     onto cylinders of the same colors.
   - So the image of `∂_c(i)` has a class that is a `→*`-descendant of the color of `i`, and
     `[W] = [U]`.
4. **Disjoint `U, W` with `[U] = [W]`.**
   - Take an expansion `e` whose cylinders partition both `U` and `W`.
   - Expand its `U`-leaves and its `W`-leaves separately to a common multiset `m*` (step 1). This
     is possible since they are disjoint. Call the result `e*`.
   - Let `σ` be a color-preserving permutation of the leaves of `e*` that exchanges its `U`-leaves
     with its `W`-leaves. Then `e*∘σ∘e*^{-1} ∈ Γ̄` maps `U` onto `W`.
5. **Arbitrary `U, W` when all nonzero classes are equal.**
   - *If `U ∪ W ≠ ∂X`:* take a nonempty clopen `Z` outside `U ∪ W`. Compose the local maps
     `U → Z` and `Z → W` from step 4.
   - *Otherwise:* pick points `p ≠ q`. Split `U = U_1 ⊔ U_2` and `W = W_1 ⊔ W_2` into nonempty
     clopens with `p ∉ U_1 ∪ W_1` and `q ∉ U_2 ∪ W_2`: put `p` in the second pieces and `q` in the
     first, using that `∂X` is perfect.
   - Map `U_1 → W_1` and `U_2 → W_2` by the first case, and patch.
6. **One color.** Here `M(𝒪) = N/⟨1 = k⟩` over the arities `k`. The nonzero classes are the
   residues modulo `gcd(k − 1)`.

**Step 4. Type (A).** With Steps 2 and 3, `Γ̄` satisfies hypotheses 1 and 2 of
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, and hypothesis 3 is assumed. That node
gives the type (A) clopen action with stabilizers `Γ̄ × Γ̄` and at most 16 pair orbits.
`type-a-action-gives-boone-higman-for-subgroups` gives the consequences for subgroups.

**Step 5. Kernel.**
- **`Γ̄ ≠ 1`.** There are finitely many colors and arbitrarily many leaves by (N). So some expansion
  `e` has two leaves `j ≠ j'` of equal color, and the transposition `e∘(j j')∘e^{-1}` moves the
  nonempty cylinder `∂_e(j)` off itself.
- **Simple `Γ`.** `N` is normal and proper, so `N = 1`.
- **Subgroups.** If `G ∩ N = 1`, then `G → Γ̄` is injective.

**Step 6. Corollaries.**
- **(a)** Combine Steps 4 and 5. For a finitely presented simple subgroup `H` of a finitely
  presented boundary-faithful clopen-transitive `Γ`, `H ≤ Γ = Γ̄`, and `Γ̄` is the actor.
- **(b), direction `⇒`.**
  - The `Γ_0`-twisted cube operad is the suboperad of `End(TOP, ⊔)` generated by:
    - the prefix insertions `C^S ⊔ C^S → C^S` at the coordinates `s ∈ S`;
    - the coordinate permutations `τ_g`.
  - Common refinements of brick partitions give the calculus of fractions.
  - Its operad group is the group of homeomorphisms that map one brick partition onto another
    piecewise by prefix maps and `τ_g`. That is `SV_{Γ_0}`, as in `pbh-full-cantor-hosts-proof`,
    acting on `C^S`.
  - This action is faithful when `Γ_0 ↷ S` is. `SV_{Γ_0}` is finitely presented by Zaremsky's
    Theorem A (`twisted-brin-thompson-finite-presentation-criterion`), and `M` has one nonzero
    class.
- **(c)** Immediate from (a) and (b).
- **Planar case.** The planar group's fractions are symmetric fractions. Its boundary image lies in
  the symmetrized `Γ̄`, which is full by Step 2.
- **Braided case.** Assume the braided operad has a symmetric quotient, obtained by forgetting
  braids to permutations.
  - The induced map onto the symmetric operad group is onto, since every permutation lifts to a
    braid.
  - Its target is nontrivial by Step 5. So a simple braided operad group maps isomorphically onto
    it. ∎
