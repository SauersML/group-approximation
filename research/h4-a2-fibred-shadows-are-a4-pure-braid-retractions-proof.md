---
rg: 2
id: h4-a2-fibred-shadows-are-a4-pure-braid-retractions-proof
kind: route
title: Proof that fibred shadows of the single-edge H_4 hexagon are pure braid shadows, and that the A_2-flat shadows are A_4 braid retractions
target: h4-a2-fibred-shadows-are-a4-pure-braid-retractions
requires: []
---

Notation is as in the target and in `h4-case1-pure-normal-form-and-fibred-obstruction` and its proof. That
includes van der Lek's local identifications (L1) and the compatibility of parabolic retractions (L2).
- `v_x` spans `ℓ_x`.
- Every `v ∈ ℂ^4` is written `v = u + t·v_x` with `u ∈ ℓ_x^⊥`.
- Each fibre wall `H_k = n_k^⊥` of `ℬ` (a wall not containing `ℓ_x`) is oriented so that `⟨n_k,v_x⟩ ≠ 0`.
- `p_k(u) := −⟨n_k,u⟩/⟨n_k,v_x⟩`.

The base point `b` lies in the real fundamental chamber, close to the point `x*` or `y*` as needed. Each local
ball of (L1) is joined to `b` by a path that stays in that real chamber.

## 1. The general shadow lemma (part (A))

**Linear identities.**
- For every fibre wall, `⟨n_k, v⟩ = ⟨n_k, v_x⟩·(t − p_k(u))`.
- For two fibre walls `i ≠ j`, put `c_{ij} := ⟨n_j,v_x⟩ n_i − ⟨n_i,v_x⟩ n_j`. Then
  `⟨c_{ij}, u⟩ = ⟨n_i,v_x⟩⟨n_j,v_x⟩·(p_j(u) − p_i(u))`.
- `c_{ij}` is non-zero (the walls differ) and `c_{ij} ⊥ v_x`. So the collision locus `{p_i = p_j}` is the
  hyperplane `c_{ij}^⊥`, and it contains `ℓ_x`.
- `c_{ij}` lies in the span of `n_i, n_j`, so `c_{ij}^⊥ ⊇ n_i^⊥ ∩ n_j^⊥`. Hence `c_{ij}^⊥` contains the
  codimension-2 flat `H_i ∩ H_j`, and it also contains `ℓ_x`.
- `ℓ_x` is modular in `ℬ`, so `H_i ∩ H_j + ℓ_x` lies in a wall of `ℬ` through `ℓ_x`, i.e. in a wall of `𝒜_x`.
  That wall is `c_{ij}^⊥`.

In particular `c_{ij}^⊥ ∈ 𝒜_x`, and on `M(ℬ)` the numbers `t, p_1(u), …, p_k(u)` are pairwise distinct. So
`Φ(v) := (t, p_1(u), …, p_k(u))` maps `M(ℬ)` into `Conf_{k+1}(ℂ)`.

**Fibrations.**
- `π : M(ℬ) → B := M(𝒜_x) ∩ ℓ_x^⊥`, `v ↦ u`, is the fibration of the source claim. Its fibre over `u` is
  `ℂ ∖ {p_1(u), …, p_k(u)}` in the coordinate `t`.
- Forgetting the first point, `Conf_{k+1} → Conf_k`, is the Fadell–Neuwirth fibration, with fibre `ℂ` minus
  `k` points.
- `Φ` covers `u ↦ (p_1(u), …, p_k(u))`, `B → Conf_k`. On each fibre it is the identity in the coordinate `t`.

Both bases are aspherical:
- every wall of `𝒜_x` contains `ℓ_x`, so `M(𝒜_x) = B × ℓ_x` and `B ≃ M(𝒜_x)`. `M(𝒜_x)` is `K(π,1)` by
  Deligne, since `𝒜_x` is the `H_3` reflection arrangement;
- `Conf_k` is `K(π,1)`.

So `π_2` of each base vanishes, and in both long exact sequences the fibre's `π_1` injects into the total space.
Let `ι : F_k → π_1M(ℬ)` be the fibre inclusion and `ι' : F_k → P_{k+1}` the standard one. Then
`Φ_* ∘ ι = ι'`, which is injective. Hence `Φ_*` is injective on `ι(F_k)`.

**The hexagon word lies in the fibre.** Let `w = α_1β_1α_2β_2α_3β_3`. Since `β_1β_2β_3 = 1`,
`w = α_1 · (β_1α_2β_1^{-1}) · ((β_1β_2)α_3(β_1β_2)^{-1})`.
- By the source claim (F-part), the image of `F` in `π_1M(ℬ)` lies in `ι(F_k)`: it is `⟨x_1,x_2,x_3⟩`, the
  meridians of the fibre points `p_1,p_2,p_3` coming from the 3 walls of `𝒜_y ∖ 𝒜_z`.
- `ι(F_k)` is normal.

So `w ∈ ι(F_k)`, and `w = 1` in `π_1M(ℬ)` iff `Φ_*(w) = 1` in `P_{k+1}`.

**Images of `F` and `N`.**
- `Φ_*ι(x_i) = ι'(x_i)` is a meridian of `t` around `p_i`, i.e. a conjugate of `A_{i,t}`. So `Φ_*(F)` is the
  stated rank-3 free factor.
- Consider the composite `P_X → π_1(B) → P_k → P_3`, where the last map keeps `p_1, p_2, p_3`. It is induced by
  `u ↦ (p_1,p_2,p_3)` modulo the diagonal.
- For `i,j ≤ 3`, `H_i` and `H_j` are walls of `𝒜_y`, so `H_i ∩ H_j ⊇ ℓ_y`. The hyperplane `c_{ij}^⊥`
  therefore contains `ℓ_x + ℓ_y`, the fixed plane of `W_Z`, so it is a wall of `𝒜_z`. The three hyperplanes
  `c_{12}^⊥, c_{13}^⊥, c_{23}^⊥` are distinct (they are the collision loci of three distinct pairs among
  distinct fibre points), so they are the 3 walls of `𝒜_z`.
- So this map factors as `M(𝒜_x) ⊂ M(𝒜_z) → Conf_3(ℂ)/ℂ`. The second map is a linear projection whose fibres
  are affine spaces, so it is a homotopy equivalence.
- Hence the composite `P_X → P_3` is `ρ^X_Z`, up to the identification `P_Z ≅ P_3`.
- By (L2), `ρ^X_Z = ρ^Y_Z ∘ ρ_Y|_{P_X}`. So `N = ker(ρ_Y|_{P_X}) ⊆ ker ρ^X_Z`. The image of `N` in `P_k`
  therefore dies when all strands except `p_1, p_2, p_3` are forgotten: `N` moves only the added points.

This proves (A). ∎

## 2. The nine `A_2` flats (part (B))

**Linear facts.** Fix `V` and `ℬ_V` as in the source claim (C): the 15 walls of `𝒜_x` plus 4 fibre walls. The
fibre walls are the 3 walls of `𝒜_y∖𝒜_z` and the third wall `n_4^⊥` of the rank-2 flat `V`.
`arrangement.py` checks the following exactly (floating point with tolerance `1e-9`, on unit root vectors):
- (a) `rank(n_1,…,n_4) = 4`;
- (b) the six vectors `c_{ij}` are roots. The three with `i,j ≤ 3` lie in `𝒜_z`, and the three `c_{i4}` lie in
  `𝒜_x∖𝒜_z`;
- (d) `𝒞_V` is not closed under its own reflections;
- (e) the multiset of the `c_{i4}` over the 9 flats covers all 12 walls of `𝒜_x∖𝒜_z`.

See `arrangement.log`.

**Coordinates.** Define `Ψ : ℂ^4 → ℂ^5/ℂ(1,…,1)` by `v ↦ (t, p_1, p_2, p_3, p_4)`.
- Suppose `Ψ(v) = 0`. Then `p_k(u) = t` for all `k`, so `⟨n_k,v⟩ = ⟨n_k,v_x⟩(t − p_k) = 0` for all four `k`.
  By (a), `v = 0`.
- The dimensions agree, so `Ψ` is a linear isomorphism.
- Under `Ψ`, the fibre wall `H_k` is `{q_0 = q_k}`, and by (b) the collision wall `c_{ij}^⊥` is `{q_i = q_j}`.
  So `Ψ(𝒞_V)` is the full `A_4` braid arrangement `{q_a = q_b : 0 ≤ a < b ≤ 4}`, and
  `M(𝒞_V) ≅ Conf_5(ℂ)/ℂ`. Hence `π_1M(𝒞_V) = P_5`.

**The retraction.** `𝒞_V ⊆ ℬ_V ⊆ 𝒜`, so `M(𝒜) ⊂ M(ℬ_V) ⊂ M(𝒞_V)`. The composite `Φ` of part 1 (with `k = 4`)
followed by the quotient by the diagonal is `Ψ` restricted to `M(ℬ_V)`, so the shadow `P → Q_V → P_5` is
`ρ_V := (M(𝒜) ⊂ M(𝒞_V))_*`.

Removing a proper analytic hypersurface from a connected complex manifold induces a surjection on `π_1`. So
`ρ_V` is onto, and so are the local maps below.

**Strand order.** At `b` (the chamber point `x + 10^{-3}(ω_2+ω_3+ω_4)`, and likewise near `y*`) the log gives
real values `p_4 < p_1 < p_2 < p_3 < t = 0`. Number the strands `1, …, 5` in this order. The path from each
local ball to `b` stays in the real fundamental chamber of `𝒜`, which lies inside one real chamber of `𝒞_V`.
So no conjugation enters the identifications below, and `A_{ij}` denotes the standard generator for the real
configuration at `b`.

**Near `y*`.** `𝒜_y` has 6 walls:
- the 3 fibre walls `{q_0 = q_k}`, `k ≤ 3`;
- the 3 walls of `𝒜_z`, which are `{q_i = q_j}`, `i,j ≤ 3`.

So `𝒜_y ⊆ 𝒞_V` is the braid arrangement on the strands `p_1,p_2,p_3,t`, i.e. strands `2,3,4,5`.
- On the (L1) ball `U_Y`: `U_Y ∩ M(𝒜) = U_Y ∩ M(𝒜_y) = U_Y ∩ M(𝒞_V)`.
- So `ρ_V|_{P_Y}` is an isomorphism onto the local group of the flat `{q_0=q_1=q_2=q_3}`.
- This strand set is consecutive in the real order, so that local group is the standard parabolic `P_{2345}`.

**Near `x*`.** `𝒞_V ∩ 𝒜_x` consists of the 6 collision walls, which form the braid arrangement on the strands
`p_1,…,p_4` = `1,2,3,4`. On `U_X`, `ρ_V|_{P_X}` is induced by `M(𝒜_x) ⊂ M(𝒞_V ∩ 𝒜_x)`, and is onto `P_{1234}`.
This map is the braid monodromy `μ`:
- The meridian of a wall `H ∈ 𝒜_x ∖ 𝒞_V` bounds a small disc transverse to `H` at a generic point, and that
  disc misses `𝒞_V`. So `μ` sends it to `1`.
- The meridian of a wall in `𝒞_V` goes to a meridian of `{q_i=q_j}`, i.e. a conjugate of `A_{ij}`.

**Kernels.**
- In the local model at `y*`, `𝒜_z = {q_i = q_j : 1 ≤ i < j ≤ 3}`. So `ρ^Y_Z` corresponds to forgetting strand `5`
  (`t`), from `P_{2345}` to `P_{234}`.
- (L2) gives `ρ_X|_{P_Y} = ρ^Y_Z`. So `F = ker ρ^Y_Z` is carried isomorphically onto
  `ker(P_{2345} → P_{234}) = ⟨A_{25},A_{35},A_{45}⟩ = F'`.
- In the local model at `x*`, `M(𝒜_x) ⊂ M(𝒞_V∩𝒜_x) ⊂ M(𝒜_z)`. So `ρ^X_Z` is `ρ_V|_{P_X}` followed by
  forgetting strand `1` (`p_4`), from `P_{1234}` to `P_{234}`. Hence `ρ_V(N) ⊆ N' = ⟨A_{12},A_{13},A_{14}⟩`.
- Conversely, let `n' ∈ N'`. Choose `g ∈ P_X` with `ρ_V(g) = n'`. Then `ρ^X_Z(g) = forget_1(n') = 1`, so
  `g ∈ N`. So `ρ_V(N) = N'`.

This proves (B). ∎

## 3. Consequences (part (C))

**The simplicial map.** Define `gA_X ↦ ρ_V(g)A_{X'}` and `gA_Y ↦ ρ_V(g)A_{Y'}` for `g ∈ P`.
- Well defined: if `gA_X = g'A_X` with `g, g' ∈ P`, then `g^{-1}g' ∈ A_X ∩ P = P_X`. Its image
  `ρ_V(g^{-1}g')` lies in `P_{1234} ⊂ B_{1234} = A_{X'}`. The same argument works for `Y`, using
  `ρ_V(P_Y) = P_{2345} ⊂ A_{Y'}`.
- Adjacency: in the Deligne complex, `gA_X` and `hA_Y` are joined iff `gA_X ∩ hA_Y ≠ ∅`, iff
  `h^{-1}g ∈ A_Y A_X`.

*Claim: `A_Y A_X ∩ P = P_Y P_X`.* Let `p = ab ∈ P` with `a ∈ A_Y` and `b ∈ A_X`.
- In `W`, `ā = b̄^{-1}`, so `ā ∈ W_Y ∩ W_X = W_Z`.
- Choose `c ∈ A_Z` with `c̄ = ā`. Then `p = (ac^{-1})(cb)`.
- `ac^{-1} ∈ A_Y` has trivial image in `W`, so it lies in `P_Y`. Likewise `cb ∈ A_X` has trivial image, so it
  lies in `P_X`.

Hence `ρ_V(h^{-1}g) ∈ P_{2345}P_{1234} ⊂ A_{Y'}A_{X'}`, and adjacency is preserved.

**Hexagons.**
- `ρ_V` is a homomorphism, so it preserves `∏α_i = ∏β_i = 1`, and by (B) it sends `F → F'` and `N → N'`.
- By (A) and (B), the hexagon word `w` is trivial in `Q_V = π_1M(ℬ_V)` iff `ρ_V(w) = 1` in `P_5`. That is the
  `A_4` single-edge hexagon relation for `(ρ_Vα_i, ρ_Vβ_i)`, with the `A_4` data
  - `F'_{A_4} = ker(ρ_{X'}|_{P_{Y'}}) = ker(forget_5 : P_{2345} → P_{234}) = F'`, and
  - `N'_{A_4} = ker(forget_1 : P_{1234} → P_{234}) = N'`.
  (For the braid arrangement, the parabolic retractions are the forgetful maps.)

*Surjectivity.* Take an `A_4` hexagon `(α'_i, β'_i)`.
- Lift `α'_1, α'_2` through the isomorphism `F ≅ F'`, and put `α_3 := (α_1α_2)^{-1}`.
- Lift `β'_1, β'_2` to `N`, using `ρ_V(N) = N'`, and put `β_3 := (β_1β_2)^{-1}`.
- Then `ρ_Vα_3 = α'_3` and `ρ_Vβ_3 = β'_3`, so `ρ_V(w) = 1`.

**Arc model.** Put the punctures `1, …, 5` of `D_5` on a horizontal diameter in the real order. Let `a_0` be the
straight arc from puncture 5 to the boundary point `∂_0` on its right, and `a_1` the straight arc from
puncture 1 to the boundary point `∂_1` on its left.
- Cutting `D_5` along `a_0` gives a disc with 4 punctures. Its mapping class group rel boundary is `B_4`,
  realised by the half-twists of punctures `1..4`, which are supported off `a_0`. Hence
  `Stab(a_0) = ⟨σ_1,σ_2,σ_3⟩ = A_{X'}`, and likewise `Stab(a_1) = A_{Y'}`.
- So `gA_{X'} ↔ g(a_0)` and `hA_{Y'} ↔ h(a_1)`. For pure `g`, `g(a_0)` starts at puncture 5, and `h(a_1)`
  starts at puncture 1.
- `gA_{X'} ∩ hA_{Y'} ≠ ∅` iff `(g(a_0), h(a_1)) = k(a_0,a_1)` for some `k`.
- `a_0` and `a_1` are disjoint. Conversely, take a disjoint pair `(e_0, e_1)` with the same endpoints. Cutting
  `D_5` along `e_0 ∪ e_1` gives a disc with 3 punctures and the same boundary pattern as for `(a_0,a_1)`. The
  pattern is: a `∂`-arc, the two sides of `e_1`, a `∂`-arc, the two sides of `e_0`. So there is a homeomorphism
  matching the patterns that is the identity on `∂D_5`, and it glues to some `k ∈ B_5` with
  `k(a_0,a_1) = (e_0,e_1)`.

So adjacency is disjointness. The hexagon's vertices are
`A_X, A_Y, α_1A_X, α_1β_1A_Y, α_1β_1α_2A_X, α_1β_1α_2β_2A_Y`, and they give the stated alternating
arc hexagon. ∎

**Remarks.**
- Part (C) says only that one `Q_V` detects exactly the `A_4` single-edge layer. It does not say that the nine
  shadows together see no more: the joint map `P → ∏_V P_5` is not analysed here.
- The `I_2(5)` data are those printed by `i25probe.py`. The statement that the shadow lies in `P_7` follows
  from (A) with `k = 6`. The section is proper because the rank of the 6 fibre normals is 4 < 6.
