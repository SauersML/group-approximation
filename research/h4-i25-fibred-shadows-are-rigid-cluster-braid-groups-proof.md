---
rg: 2
id: h4-i25-fibred-shadows-are-rigid-cluster-braid-groups-proof
kind: route
title: Proof that the fibred I_2(5) shadows of the single-edge H_4 hexagon are the rigid-cluster subgroups f^{-1}(Δ²) of P_7
target: h4-i25-fibred-shadows-are-rigid-cluster-braid-groups
requires:
  - h4-a2-fibred-shadows-are-a4-pure-braid-retractions
---

Notation is as in the target, and in part 1 (the general shadow lemma) of
`h4-a2-fibred-shadows-are-a4-pure-braid-retractions-proof`. That lemma supplies:
- `⟨n_k,v⟩ = ⟨n_k,v_x⟩(t − p_k(u))`;
- the collision vector `c_{ij} = ⟨n_j,v_x⟩n_i − ⟨n_i,v_x⟩n_j`, with `{p_i = p_j} = c_{ij}^⊥`;
- the fact that the hexagon identity in `π_1M(ℬ)` is equivalent to the identity in `P_{k+1}`;
- `N = ker ρ^X_Z`, from (L2).

## 1. The rigid cluster (general mechanism)

Let `V = w ∩ w'` be any rank-2 flat with `w ∈ 𝒜_y∖𝒜_z` and `w' ∈ 𝒜_x∖𝒜_z`.

*`w'` is the only wall of `V` that contains `ℓ_x`.* Suppose two distinct walls of `V` both contain `ℓ_x`. Then both
contain `V + ℓ_x`, which is a hyperplane because `ℓ_x ⊄ V` (as `ℓ_x ⊄ w`). So the two walls are equal.

Hence every other wall of `V` is a fibre wall: `w` (giving `p_c`) and the `m − 2` remaining walls (giving
`q_j`). All their normals lie in the plane `Π = span(n_c, w')`, which is `V^⊥`.
- Write `n_{q_j} = a_j n_c + b_j w'`. Since `⟨w',v_x⟩ = 0`, we get `⟨n_{q_j},v_x⟩ = a_j⟨n_c,v_x⟩`, and
  `a_j ≠ 0`.
- So `q_j(u) = p_c(u) − (b_j/a_j)·⟨w',u⟩/⟨n_c,v_x⟩ = p_c(u) + κ_j s(u)`.
- The `κ_j` are pairwise distinct and non-zero, because the walls are distinct.
- For `i ≠ j` in the cluster `C = {p_c, q_1, …}`, the vector `c_{ij}` lies in `Π` and is orthogonal to `v_x`.
  The only such direction in `Π` is `w'`, because `n_c` is not orthogonal to `v_x`. So all pairs of `C`
  collide exactly on `w'`.

`i25cluster.py` gives the following for the three fibred `I_2(5)` flats (`m = 5`):
- the cluster normals have rank 2;
- the full-cluster collision wall is the wall of `V` through `ℓ_x`;
- `κ = {0, 1, 0.618034, 1.618034}`;
- the 5 normals lie at `18°, 54°, 90°, 126°, 162°` in `Π`;
- the list of 10 collision walls is as stated in (1). In particular each pair `{p_a or p_b, q_j}` collides on
  its own wall of `𝒜_x∖𝒜_z`, and the pairs among `p_1, p_2, p_3` collide on `𝒜_z`;
- the rank of all 6 fibre normals is 4.

That `ℓ_x` is modular in these `ℬ_V` is the filter in `i25probe.py`: every `c_{ij}` is a wall of `𝒜_x`.

## 2. The shadow `G_V`

Let `Ψ : ℂ^4 → ℂ^7/ℂ(1,…,1)` be `v ↦ (t, q_1, q_2, q_3, p_1, p_2, p_3)`.
- `Ψ` is injective. If `Ψ(v) = 0`, then all `p_k = t`, so `v ⊥` all 6 fibre normals. Their rank is 4, so
  `v = 0`.
- Its image `L` is contained in `R := {cluster = p_c + s·(0, κ_1, κ_2, κ_3)}`, which is parametrised by
  `(t, p_a, p_b, p_c, s)` modulo the diagonal. So `dim R = 4 = dim L`, and `L = R`.
- `Ψ^{-1}` of the `A_6` braid walls is the set of fibre walls and collision walls, i.e. `𝒞'_V`. So
  `Ψ : M(𝒞'_V) ≅ R ∩ Conf_7/ℂ`.

Let `f : Conf_7 → Conf_C` forget `t, p_a, p_b`. It is a Fadell–Neuwirth fibration, with fibre
`Conf_3(ℂ ∖ 4 points)`. Put `O := {p_c + s(0,κ) : p_c ∈ ℂ, s ∈ ℂ^*} ⊂ Conf_C`. Then `R ∩ Conf_7 = f^{-1}(O)`,
and restricting `f` gives a fibration `f^{-1}(O) → O ≃ S^1` with the same fibre.

Compare the two long exact sequences, using that `π_2` vanishes for `O` and for `Conf_C`:
- `1 → K → π_1 f^{-1}(O) → ℤ → 1`;
- `1 → K → P_7 → P_C → 1`.

The generator of `π_1 O = ℤ` is `s ↦ e^{iθ}s`, the rigid rotation of the cluster, which is `Δ²_C`. It has
infinite order in `P_C`. By the five lemma, `π_1 f^{-1}(O) → P_7` is injective, and its image is
`f_*^{-1}(⟨Δ²_C⟩)`. Since `Δ²_C` is central in `P_C`, this subgroup does not depend on the base point.

Dividing by the scaling (`s = 1`) gives `f^{-1}(O)/ℂ ≅ ℂ^* × Conf_3(ℂ ∖ {0, κ_1, κ_2, κ_3})`.

**The shadow.**
- `M(𝒜) ⊂ M(ℬ_V) ⊂ M(𝒞'_V)`. The composite `P → π_1M(𝒞'_V) ≅ G_V` is `ρ_V`.
- `ρ_V` is onto, because removing hypersurfaces is surjective on `π_1`.
- By the shadow lemma (with `k = 6`), the `ℬ_V` hexagon identity is equivalent to `ρ_V(ω) = 1` in `P_7`, where `ω = α_1β_1α_2β_2α_3β_3` is the hexagon word.

## 3. Local images

The base point `b` lies in the real fundamental chamber. `i25cluster.log` gives the real order
`q_* < q_* < q_* < p_1 < p_2 < p_3 < t` for all three flats. The chamber of `𝒜` lies in a single chamber of
`𝒞'_V`, so no conjugation enters.

**Near `y*`.** The walls of `𝒞'_V` through `y*` are those of `𝒜_y`:
- `t = p_i`, for `i ≤ 3`;
- `p_i = p_j`, for `i, j ≤ 3`.

In `R`, the coordinates `(t, p_1, p_2, p_3)` vary freely near `y*` modulo translation, with `s ≠ 0` and the
`q`'s far away. So `U_Y ∩ M(𝒞'_V)` is the local `Conf_4` of strands `4, 5, 6, 7`, which are consecutive.
- Hence `ρ_V|_{P_Y} ≅ P_{4567}`.
- `ρ^Y_Z` is forgetting `t` (strand 7), because the walls of `𝒜_z` are `p_i = p_j`. So
  `ρ_V(F) = ker(P_{4567} → P_{456}) = ⟨A_{47},A_{57},A_{67}⟩`.

**Near `x*`.** The walls through `x*` are the 10 collision walls, forming the arrangement `coll`, and `t` stays
away. Repeat the argument of §2 in `ℓ_x^⊥`, with `u ↦ (q_1,q_2,q_3,p_1,p_2,p_3)` modulo the diagonal. The
dimension count is `(p_a,p_b,p_c,s)` modulo the diagonal `= 3`, and the fibre is `Conf_2(ℂ ∖ 4 points)`. It
gives `π_1M(coll) ≅ f'^{-1}_*(⟨Δ²_C⟩) = G^X_V ⊂ P_{1…6}`. Here the strand set is `C = {1,2,3,c+3}`, and `f'`
forgets `p_a, p_b`.
- `P_X ↠ π_1M(coll)`, since `M(𝒜_x) ⊂ M(coll)`. So `ρ_V(P_X) = G^X_V`.

**The kernel `N`.** The walls of `𝒜_z` are the collisions among `p_1, p_2, p_3`. So `ρ^X_Z` is `ρ_V|_{P_X}`
followed by `g ↦ g|_{456}`. Hence `ρ_V(N) ⊆ N_V`.

Conversely, let `n ∈ N_V`. Lift it to `g ∈ P_X`. Then `ρ^X_Z(g) = n|_{456} = 1`, so `g ∈ N`. Hence
`ρ_V(N) = N_V`.

## 4. The consequence

The argument of part 3 of the companion proof applies verbatim:
- `A_YA_X ∩ P = P_YP_X`;
- `ρ_V(P_X) ⊂ P_{1…6} ⊂ A_{X''}` and `ρ_V(P_Y) = P_{4567} ⊂ A_{Y''}`.

This gives the type-preserving simplicial map.

In `B_7`, the single-edge data for `(X'', Y'')` are:
- `F_{A_6} = ker(ρ_{X''}|_{P_{Y''}}) = ker(P_{4567} → P_{456}) = ρ_V(F)`, since braid parabolic retractions
  forget strands;
- `N_{A_6} = ker(ρ_{Y''}|_{P_{X''}}) = ker(P_{1…6} → P_{456}) ⊇ N_V`.

The identity is equivalent to `ρ_V(ω) = 1`, by §2.

Surjectivity onto the constrained hexagons:
- lift `α'_1, α'_2` through `F ≅ ρ_V(F)`;
- lift `β'_1, β'_2` through `N ↠ N_V`;
- close up with `α_3 = (α_1α_2)^{-1}` and `β_3 = (β_1β_2)^{-1}`.

For an `A_2` flat (`m = 3`), §1 gives a 2-point cluster, and `f^{-1}(⟨Δ²_2⟩) = P_5` because `P_2 = ⟨Δ²_2⟩`.
This agrees with the companion claim. ∎
