---
rg: 2
id: commensurator-rigid-no-faithful-bs-member-proof
kind: route
title: Commensurator rigidity gives a virtually free kernel of the commensurator map, whose centralizer in a vertex group acts trivially on the tree
target: commensurator-rigid-groups-have-no-faithful-bs-members
---

Let `H ∈ BS_G` act on its Bass--Serre tree `X`, which has no inversions. Fix a
vertex `v` with stabilizer `G_v`.

1. **Commensurability of stabilizers.** Adjacent vertex stabilizers meet in the
   edge stabilizer, which has finite index in both. Along a path, the intersection
   stays of finite index. So all vertex stabilizers `G_x` are pairwise commensurable
   subgroups of `H`, and `H` commensurates `G_v`. `X` is locally finite, and
   `H\X` is finite.
2. **The commensurator map.** Put `Φ: H -> Comm(G_v)`, sending `h` to the class of
   conjugation by `h`, restricted to `G_v ∩ h^(-1) G_v h`. It is a homomorphism,
   and on `G_v` it is the inner-automorphism map.
3. **Finite index of `Φ(G_v)`.** Choose finite-index `L_1 <= G_v` and `L_2 <= G`
   with an isomorphism `L_1 ≅ L_2`. The restriction isomorphisms
   `Comm(G_v) ≅ Comm(L_1) ≅ Comm(L_2) ≅ Comm(G)` send `Φ(L_1)` to the inner
   image of `L_2`. That image has finite index in the inner image of `G`, since
   the map is injective and `[G : L_2] < ∞`. The inner image of `G` has finite
   index in `Comm(G)` by hypothesis. So `[Comm(G_v) : Φ(G_v)] < ∞`, and
   `M := Φ^(-1)(Φ(G_v)) = N G_v`, with `N := ker Φ`, has finite index in `H`.
4. **`N` has finite vertex stabilizers.** Let `x` be a vertex. An element of `N ∩ G_x`
   centralizes a finite-index subgroup of `G_v`, hence of `G_x`. Let `VC(G_x)` be the
   normal subgroup of elements of `G_x` that centralize a finite-index subgroup of
   `G_x`. Choose finite-index `P_1 <= G_x`, `P_2 <= G` with `P_1 ≅ P_2`, and let
   `P` be the normal core of `P_1` in `G_x`. An element of `VC(G_x) ∩ P` goes to an
   element of `P_2` centralizing a finite-index subgroup of `G`, which is trivial
   because `G -> Comm(G)` is injective. So `VC(G_x)` meets `P` trivially and
   injects into the finite group `G_x/P`. Hence `N ∩ G_x <= VC(G_x)` is finite.
5. **`N` is finitely generated.** `M` has finite index in `H`, so `M\X` is
   finite. For a vertex `y`, `M y = ⋃_{g ∈ G_v} N g y`, and `G_v y` is finite
   because `G_v ∩ G_y` has finite index in `G_v`. So `N\X` is finite. `N` acts on
   the locally finite tree `X` cocompactly with finite stabilizers, so `N` is
   finitely generated (Bass--Serre: the fundamental group of a finite graph of
   finite groups).
6. **The centralizer.** Each `n ∈ N` has trivial image in `Comm(G_v)`, so it
   centralizes a finite-index subgroup of `G_v`. With generators `n_1, ..., n_k`,
   the centralizer `C := C_(G_v)(N)` contains the intersection of `k`
   finite-index subgroups, so it has finite index in `G_v`.
7. **A trivially acting subgroup.** Let `Z` be a finite set of representatives of
   the `N`-orbits of vertices, and put `C' := C ∩ ⋂_{z ∈ Z} G_z`. It has finite
   index in `G_v` by step 1. For a vertex `y = n z` with `n ∈ N` and `z ∈ Z`, and
   `c ∈ C'`, we get `c y = c n z = n c z = n z = y`. So `C'` fixes every vertex,
   and it is nontrivial because `G_v` is infinite (it is commensurable with the
   infinite group `G`). So the action of `H` on `X` is not faithful.

Every step is elementary apart from the Bass--Serre structure theorem used in step
5. The instances on the claim node use the cited rigidity theorems of Farb--Handel
and Ivanov only to verify the hypothesis.
