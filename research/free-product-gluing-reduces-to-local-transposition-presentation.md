---
rg: 2
id: free-product-gluing-reduces-to-local-transposition-presentation
kind: claim
title: Type-changing transpositions of V times a free product action lift coherently to the free-product gluing group through B-interleaved ladders, so the free-product presentation FPG follows from the Quick-type local transposition presentation of the full group whenever cylinders have no nontrivial setwise stabilizers (full shifts over torsion-free free products); a direct check confirms FPG for PSL(2,Z) on two points
requires:
  - free-product-gluing-equals-splitting-of-the-gluing-kernel
  - v-times-free-product-gluing-kernels-split-over-the-factors
  - v-times-full-groups-have-local-transposition-presentations
distinct_from:
  free-product-gluing-equals-splitting-of-the-gluing-kernel: that shows FPG is equivalent to the splitting of the gluing kernel and locates the open part in type-changing elements; this lifts every type-changing transposition canonically, verifies the local relations for the lifts, and so reduces FPG to the local transposition presentation.
  v-times-full-groups-have-local-transposition-presentations: that states the Quick-type presentation of F(T) and needs lifts in the gluing group Γ~; this lifts into the smaller quotient G_* = Γ~/⟨⟨factor kernels⟩⟩, where every factor's full group is available, and checks all four relation families there.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-18; lane proof, elementary; not reviewed; no priority
claimed). It answers the coordinator's question on type-changing elements: they lift coherently, and no
counterexample exists in any finite tree-like or flat configuration. What remains of FPG is the
Quick-type local presentation LTP of the full group itself. That is the same object bh-p2b-exact needs
for Z. **LTP, FPG in general and EX(Z) stay OPEN.**

## Setting

- Notation is that of `free-product-gluing-equals-splitting-of-the-gluing-kernel`:
  - `Λ = Λ_1 * Λ_2` acts on `X`, with `Ω = C × X`;
  - the groups are `F = F(T)`, `F_i = F(T_i)` and `B = LC(X, V)`;
  - `G_* = F_1 *_B F_2 / ⟨⟨disjoint-support commutators⟩⟩`, with `θ : G_* → F`.
- A **piece** is `[u] × P`, with `P` a cylinder.
- A **labelled transposition** `[α|β]_λ` swaps disjoint pieces `α = [u] × P` and `β = [u'] × λP` by
  `(uw, x) ↦ (u'w, λx)`.
- A label is **single-factor** if it lies in `Λ_1 ∪ Λ_2`. The label `1` counts as lying in both factors.
- Single-factor labelled transpositions lie in `F_1` or in `F_2`, and so in `G_*`.

## Statement

1. **Room lemma.** Let `a ∈ F_2` have support `S`, and let `g ∈ F_1` restrict on `S` to an arrow with
   label 1. Suppose `u ∈ B` agrees with `g` on `S`; such a `u` exists when no fibre of `S` or of `gS` is
   all of `C`. Then `g a g^-1 = u a u^-1` in `G_*`, and the right side is computed inside `F_2`. The same
   holds with the factors exchanged.
2. **Ladder lemma.** A **ladder** is a sequence of pairwise disjoint pieces `Y_0, …, Y_k` with
   single-factor labels `ℓ_j` on the edges `Y_(j−1) → Y_j`, where `Y_j = [w_j] × (ℓ_j ⋯ ℓ_1) P_0` and any
   two consecutive labels lie in a common factor.
   - The labelled transpositions `s_j = [Y_(j−1)|Y_j]_(ℓ_j)` generate a subgroup of `G_*`.
   - `θ` maps it isomorphically onto `Sym(Y_0, …, Y_k)`, which acts with the canonical path labels.
3. **Canonical lifts.** Let `λ = ℓ_1 ⋯ ℓ_m` be the reduced form of a nontrivial label. Every `[α|β]_λ` has
   a **B-interleaved ladder** from `α` to `β`: syllable edges `ℓ_m, …, ℓ_1`, with a label-1 edge before,
   between and after them. Its lift `L[α|β]_λ` is the ladder word for the transposition `(α β)`. Then:
   - `L` does not depend on the ladder;
   - a ladder for any word representing `λ`, reduced or not, gives the same element.
4. **The local relations lift.**
   - The lifts satisfy (O) and the split relations (S_C) and (S_X) of
     `v-times-full-groups-have-local-transposition-presentations`.
   - They satisfy the conjugacy relations (C) in every configuration where the two transpositions have
     disjoint supports, or share exactly one piece.
   - Under hypothesis (H) below, (C) also holds when they share both pieces.
   - After splitting, every (C) configuration is of one of these three kinds.
5. **Theorem.** Assume:
   - **(H)** if `ν ∈ Λ ∖ 1` and `νP = P` for a cylinder `P`, then `P = X`;
   - **LTP(F)**: `F` is presented by labelled transpositions subject to (O), (C), (S_C) and (S_X).

   Then FPG holds. (H) holds for the full shift `A^Λ` over a torsion-free `Λ`, in particular over `F_n`.
   Hence, with `free-product-gluing-equals-splitting-of-the-gluing-kernel` item 4:

   > exactness over `F_n` ⇐ LTP(F(T_(F_n, A^(F_n)))) ∧ EX(Z),

   and so over every `n`-generated group, including the Track A group, by rank universality.
6. **PSL(2, Z), direct check.** Let `Λ = ⟨a⟩ * ⟨b⟩ ≅ Z/2 * Z/3` act on `X = {0, 1}`, with `a` swapping and
   `b` fixing both points. Then FPG holds, and `F ≅ V(Z/3 * Z/3)`, the index-2 subgroup.

## Proof

**1.**
- `u^-1 g ∈ F_1` is the identity on `S`, so it is supported off `S`.
- Hence `u^-1 g` commutes with `a` in `G_*`, by disjoint commutation.
- So `g a g^-1 = u (u^-1 g) a (u^-1 g)^-1 u^-1 = u a u^-1`, and `u ∈ B ≤ F_2`.
- *Existence of `u`.* `g|_S` preserves fibres. Extend it fibrewise by a prefix bijection between the
  complements `C ∖ S_x` and `C ∖ (gS)_x`, which are both nonempty. The choice is locally constant in
  `x`.

**2.** `Sym(k+1)` has the Coxeter presentation on adjacent transpositions (Moore): `s_j^2`,
`(s_j s_(j+1))^3`, and `(s_j s_l)^2` for `|j − l| ≥ 2`. Each relation holds in `G_*`:
- `s_j^2`, inside `F_1` or `F_2`;
- `(s_j s_(j+1))^3`: the two labels lie in a common factor `i`, so both transpositions lie in `F_i`, where
  the relation holds because `F_i ≤ F`;
- `(s_j s_l)^2`: the supports are disjoint, so the relation holds inside one `F_i` or by disjoint
  commutation.

So `⟨s_j⟩ ≤ G_*` is a quotient of `Sym(k+1)`. The labels form a coboundary (`c_j = ℓ_j ⋯ ℓ_1`), so the
permutations of the `Y_j` with labels `c_(σ j) c_j^-1` form a subgroup of `F` isomorphic to `Sym(k+1)`,
and `θ` maps `⟨s_j⟩` onto it. Hence the quotient map is an isomorphism.

**3.**
- *Moving one intermediate piece.* Let `Ã` have the same `X`-part as an intermediate piece `A`, and be
  disjoint from the whole ladder. Insert `Ã` next to `A` by two label-1 edges. The result is again a
  ladder.
  - In its symmetric group, the transposition that joins `A`'s neighbour to `Ã` is a conjugate by
    `(A Ã)`. This is a relation among three elements of one `F_i`, since `B ≤ F_i`.
  - So the ladder with `Ã` in place of `A` has its generators in the image of the enlarged `Sym`. Both
    ladder words then represent `(α β)` there, and by 2 they are equal in `G_*`.
- *Arbitrary ladders.* Two ladders are compared through a third one disjoint from both. Room is available
  after one (S_C) split of any piece with a full fibre.
- *Non-reduced words.* Suppose two consecutive syllable edges have labels `ℓ` and `ℓ'` in one factor `i`.
  - Every transposition of that sub-path, B-links included, lies in `F_i`. So replacing the sub-path by a
    direct edge labelled `ℓℓ'` is a relation inside `F_i`, or a B-edge when `ℓℓ' = 1`.
  - The rest of the argument is as for moving pieces. Induct on the number of cancellations.

**4.**
- *(O).* A lift is the image of a transposition of `Sym`.
- *(S_C) and (S_X).* Split every piece of a ladder for `t`, giving two disjoint ladders. Each generator
  `s_j` splits in its own `F_i` as `s_j^0 s_j^1`, and the halves commute. So `s_j ↦ s_j^0 s_j^1` is the
  diagonal map `Sym(ℒ) → Sym(ℒ_0) × Sym(ℒ_1)`, and `L(t) = L(t_0) L(t_1)`. The `X`-direction split is the
  same, since the `X`-parts of a ladder split along with `P = P_1 ⊔ P_2`.
- *(C), disjoint supports.* Choose the two ladders disjoint. Their generators commute pairwise, inside one
  `F_i` or by disjoint commutation.
- *(C), one shared piece.* Take `t = [α|β]_λ` and `t' = [β|δ]_μ`. Their canonical ladders end and start
  with label-1 edges, so the concatenation `α … β … δ` is a ladder. In its `Sym`,
  `t' t t'^-1 = (α δ)`, with path label `μλ`. By 3, that ladder word is `L[α|δ]_(μλ)`.
- *(C), both pieces shared.* Take `{α, β} = {γ, δ}` with labels `λ ≠ μ`. Then `ν = λ^-1 μ` satisfies
  `νP_α = P_α`, so `P_α = X` by (H).
  - Every piece of both ladders can then be taken to be a full column `[w] × X`. All generators lie in
    `M_1 ∪ M_2`, where `M_i = V(Λ_i)`.
  - The point case gives a homomorphism `M = V(Λ) = V(Λ_1) *_V V(Λ_2) / ⟨⟨cc⟩⟩ → G_*`
    (`v-times-free-product-gluing-kernels-split-over-the-factors`, item 5). Composed with `θ` it is the
    inclusion `M ≤ F`, so it is injective.
  - The relation holds in `F` between elements of its image, so it holds in `G_*`.
- *Reduction.* By (S_C) and (S_X), the pieces of `t` can be split until each is disjoint from, or equal
  to, a piece of `t'`. Quick's partial action applies exactly when the images are pieces.
- *(H) for full shifts.* If `ν Z(F, p) = Z(F, p)` with `F ≠ ∅`, then `νF = F`, so `ν^(|F|!)` fixes `F`
  pointwise under left multiplication. That forces `ν^(|F|!) = 1`, and so `ν = 1` when `Λ` is torsion-free.

**5.**
- Define `Φ` on the LTP generators by `Φ[α|β]_λ = L[α|β]_λ`. By 4, `Φ` respects every relation of LTP, so
  it is a homomorphism `F → G_*` with `θ Φ = id`.
- Each single-factor transposition is its own lift, and `F_1 ∪ F_2` is generated by such transpositions
  (`v-times-ample-full-groups-are-generated-by-transpositions`, applied to `T_i`). So `Φ θ` is the
  identity on generators of `G_*`, and `θ` is an isomorphism.
- The displayed consequence is item 4 of the equivalence node.

**6.**
- *The `C`-picture.* Identify `Ω = C × {0} ⊔ C × {1}` with `C` through `C_0, C_1`.
  - `F_1 = F(G_V × (Z/2 ⋉ X)) ≅ V`, and its arrows carry trivial `H`-labels for the transversal `{1, a}`.
  - `F_2 = V(⟨b⟩)` on `C_0` times `V(⟨aba⟩)` on `C_1`.
  - `B = V_(C_0) × V_(C_1)` and `F ≅ V(H)` with `H = ⟨b⟩ * ⟨aba⟩ ≅ Z/3 * Z/3`.
- *Labels on every cone.* For a cone `W`, define `b|_W = v b|_(v^-1 W) v^-1` with `v ∈ V = F_1` and
  `v^-1 W ⊆ C_0`. By 1 this is independent of `v`: two choices differ by an element supported off
  `v^-1 W`, or by an element of `V_(C_0) ≤ B` inside `F_2`.
- *The relations of `V(⟨b⟩)`.* They hold after conjugating everything into `C_0`: disjoint commutation,
  splitting and `b^3 = 1`. The same holds for `aba` through `C_1`.
- *The label commutators.* `[b|_U, (aba)|_(U')]` for disjoint `U, U'` is conjugate to a
  disjoint-support commutator.
- *Conclusion.* `G_*` is a quotient of `V(⟨b⟩) *_V V(⟨aba⟩) / ⟨⟨cc⟩⟩ ≅ V(H) = F`, by the point case of
  FPG for two factors. It also maps onto `F`, so `θ` is an isomorphism. ∎

## Lesson for general BH

**Free products cost nothing beyond locality.** A type-changing transposition, which crosses from one
factor's dynamics to the other's, lifts canonically by a B-interleaved ladder. Every factor change
passes through a trivial-label link, so each Coxeter relation involves one factor only. No free-product
obstruction is left in any flat configuration.

Cycles with nontrivial holonomy occur only on full columns when cylinders have no setwise stabilizers.
There the point case, `V(Λ_1 * Λ_2)`, already holds.

So for `F_n` and the Track A groups, P2′b is exactly one object: the Quick-type local transposition
presentation of the full group, with overlapping supports. That is the same object the cyclic case
EX(Z) needs. The non-amenable case is no harder than the amenable one; it is the same problem.
