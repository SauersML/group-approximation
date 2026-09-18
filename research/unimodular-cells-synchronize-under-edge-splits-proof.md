---
rg: 2
id: unimodular-cells-synchronize-under-edge-splits-proof
kind: route
title: Synchronization of edge-split descendants in every rank, by a half-tube shared vertex at generic points and induction over the rational stratum of the point
target: unimodular-cells-synchronize-under-edge-splits
requires:
  - half-tube-lattice-points-are-edge-split-vertices
  - edge-splits-cut-every-rational-hyperplane
  - rank-two-synchronization-off-totally-irrational-rays
---

Lane bh-free-61, 2026-09-18. Lane proof, elementary, not independently reviewed.

## What is proved

For every `m ≥ 1`, every point `x ∈ Ŝ_m`, and all cells `C_1, C_2` whose clopens contain
`x`, some cell in `Desc(C_1) ∩ Desc(C_2)` has a clopen containing `x`. Call this
**local synchronization**, `LS_m`.

By the local form in `unimodular-cells-synchronize-under-edge-splits` (compactness, then
disjointify with the cut lemma), `LS_m` for pairs `c ⊆ C` is `(Sync_m)`. So `(Sync_m)`
holds for every `m`.

The proof is by induction on `m`. `LS_0` is trivial, and `LS_1` is Serret's theorem
together with factor-closedness of the Stern–Brocot tree.

## Notation

- `Desc(K)` is the set of iterated edge-split descendants of a cell `K`. Descendants of
  a common descendant are common descendants.
- For a cell `K` with ray `g`, the *link* at `g` is `Z^{m+1}/Zg`, and the *corner* of `K`
  at `g` is the image cone. Rational hyperplanes of the link are the images of rational
  hyperplanes through `g`.
- A point `x ∈ Ŝ_m` lies *over* the ray `ξ` when `ξ` is in the closure of every member of
  `x`. Let `W(x)` be the smallest rational subspace containing `ξ`. The point is
  *generic* when `W(x) = R^{m+1}`. A generic point is the unique point over its ray, and
  it lies in a cell exactly when `ξ` is in the cell's interior.

## Step 1. Generalized vertex lemma (every `m`)

**Claim.** Let `c' ⊆ f` be cells sharing the ray `g`. Suppose the corner of `c'` at `g` is a
link descendant of the corner of `f`. Then `c' ∈ Desc(f)`.

- Each link split of a corner along `(ā, b̄)` is realized by splitting the cell along
  `(a, b)`: the new ray `a + b` has image `ā + b̄`.
- The splitting hyperplane contains `g`, and the corner of `c'` lies in one link child. So
  `c'` lies in the corresponding cell child. Following the link chain from the corner of
  `f` to the corner of `c'` gives `f'' = cone(g, a''_1, …, a''_m) ⊇ c'` with the same corner
  as `c'`.
- Each ray `p_i` of `c'` other than `g` then satisfies `p_i = a''_i + x_i g` with `x_i ≥ 0`.
  Splitting `x_i` times along `(g, a''_i)`, keeping the child that replaces `a''_i` by
  `a''_i + g`, keeps `c'` inside, since at every point of `c'` the coefficient of `g` is
  at least that of `a''_i` while `x_i ≥ 1`. The result is `c'`.

For `m = 2` every unimodular subcone of a rank-two corner is a link descendant, and this
is the vertex lemma, part 2 of `rank-two-synchronization-off-totally-irrational-rays`.

## Step 2. Shared ray implies a common descendant at generic points

**Claim** (assuming `LS_{m−1}` at generic points). Let `x` be generic over `ξ`. Let
`c_1 ∈ Desc(C_1)` and `f_1 ∈ Desc(C_2)` both contain `x` and share a ray `g`. Then some cell of
`Desc(c_1) ∩ Desc(f_1)` contains `x`.

This is part 5 (⇐) of the rank-two node with the Stern–Brocot step replaced by `LS_{m−1}`.
- `ξ` is interior to `Q = c_1 ∩ f_1`, a pointed polyhedral cone with extreme ray `g`. The
  link point `ξ̄` is generic in the link. By `LS_{m−1}` it lies in a common link
  descendant `λ_0` of the two corners.
- By cofinality (`edge-splits-cut-every-rational-hyperplane`), the descendants
  `λ = cone(p̄_1, …, p̄_m)` of `λ_0` containing `ξ̄` shrink to `ξ̄`. They are common link
  descendants.
- Let `p_i` be the least lift of `p̄_i` lying in `Q`. The fibre `p̄_i + Rg` meets `Q` in a ray
  `[e_i, ∞)` with `e_i ∈ ∂Q`, and `p_i − e_i = θ g` with `0 ≤ θ < 1`. As `λ` shrinks,
  `|p_i| → ∞`. So `p̂_i` converges projectively to `ẑ`, the point where the fibre of `ξ̄`
  leaves `Q` in the direction `−g`. That point lies strictly beyond `ξ̂` as seen from `ĝ`.
- Write `ξ = αg + Σ β_i p_i` with all `β_i > 0`. The point `Σ β_i p_i = ξ − αg` lies on the
  fibre of `ξ̄` and projectively tends to `ẑ = [ξ − s_0 g]` with `s_0 > 0`. So `α > 0` for
  deep `λ`, and `ξ` is interior to `cone(g, p_1, …, p_m) ⊆ Q`.
- `(g, p_1, …, p_m)` is a basis, since `λ` is unimodular in the link. By Step 1 the cone
  lies in `Desc(c_1) ∩ Desc(f_1)`.

## Step 3. Generic points

**Claim.** `LS_m` holds at generic points (assuming `LS_{m−1}` at generic points).

- For `m ≥ 2`, the shared-vertex corollary of `half-tube-lattice-points-are-edge-split-vertices`
  gives `c_1 ∈ Desc(C_1)` and `f_1 ∈ Desc(C_2)`, both containing `ξ` and sharing a vertex `w`.
- Step 2 finishes.
- For `m = 1` this is Serret's theorem.

## Step 4. Points over a proper rational subspace

Let `x` lie over `ξ` with `W = W(x)` of dimension `k + 1 ≤ m`, and put
`Λ_W = W ∩ Z^{m+1}` and the quotient lattice `Z^{m+1}/Λ_W` of rank `m − k`.

**Faces in `W`.** Cut `C_s` by finitely many rational hyperplanes `H_l ⊇ W` with
`∩ H_l = W` (cut lemma). Let `p_s` be the piece whose clopen contains `x`.
- `p_s` lies on one side of each `H_l`, and `ξ` is in its closure. So `σ_s = p̄_s ∩ W` is a
  face of `p_s` containing `ξ`.
- Its span is a rational subspace containing `ξ`, hence equal to `W`. So `σ_s` is spanned by
  `k + 1` of the rays of `p_s`, which form a basis of `Λ_W`, and `ξ` lies in its relative
  interior.

**Transverse images.** For a cell `K` with a face `σ ⊂ W` spanned by rays of `K` and with
`ξ ∈ relint σ`, let `τ̄_K` be the image of `K` in `R^{m+1}/W`, a unimodular cone of the
quotient lattice. Let `x̄` be the point of the quotient Cantorization whose members are
the sets `U` with `π^{-1}(U) ∈ x`.
- `x ∈ K` if and only if `x̄ ∈ τ̄_K`. Near `ξ`, `K` coincides with `π^{-1}(τ̄_K)`, and every
  rational polyhedral open cone around `ξ` belongs to `x`.
- In particular, changing a transverse ray `t` of `K` by an element of `Λ_W`, when this
  keeps `σ` and the image, does not change whether `x ∈ K`.

**The argument.**
1. **Common face.** In `W`, the point `ξ` is generic. By Step 3 in rank `k + 1` (or
   trivially if `k = 0`), `σ_1` and `σ_2` have a common `W`-descendant `σ ∋ ξ`.
   - Realize its splits on `p_s` by splitting along pairs of face rays. The children's
     faces are the `W`-children, and `x` goes with the one whose face contains `ξ`,
     because the other child's closure misses `ξ`.
   - This gives `K_s ∈ Desc(p_s)` with face `σ` and `x ∈ K_s`.
2. **Common transverse cone.** By `LS_{m−k−1}` at `x̄`, the images `τ̄_{K_1}` and `τ̄_{K_2}`
   have a common quotient descendant containing `x̄`.
   - Realize it by splitting along pairs of transverse rays. The splitting hyperplane
     contains `W`, the face `σ` is kept, and `x` follows `x̄`.
   - This gives `K'_s = cone(σ, T^{(s)})` with the same face and the same transverse image.
3. **Match the lifts.** `T^{(1)}_j − T^{(2)}_j ∈ Λ_W = Zσ`. Take `N` so large that
   `T''_j = T^{(1)}_j + N Σ_i σ_i` exceeds both lifts in `Z_{≥0}σ`.
   - Raise each `T^{(s)}_j` to `T''_j` by splits along `(σ_i, T_j)`, keeping the child that
     replaces `T_j` by `T_j + σ_i`. This keeps the face and the image, so it keeps `x`.
   - `cone(σ, T'')` lies in `Desc(K'_1) ∩ Desc(K'_2)` and contains `x`.

Both inputs are lower rank: `k + 1 ≤ m` in step 1 and `m − k ≤ m` in step 2. This closes
the induction. For `m = 2`, Step 4 with `k = 0` is part 3 and with `k = 1` is part 4 of the
rank-two node.

## Consequences and what is not claimed

- `(Sync_m)` holds for every `m`. Equivalently, the poset of unimodular dissections of
  `Ŝ_m`, ordered by descent, is directed. This is the synchronization input for
  `rational-projective-full-groups-are-finitely-presented`, in every rank, including
  `m = 6g − 7`.
- **Not claimed.** The step recorded in that gate node's Attempt 4 is not addressed: every
  dissection of a cell into its descendants must be refined by a split tree of the cell
  whose leaves inside each piece form a split tree of that piece. That is a hierarchy
  statement of the same kind as `edge-split-dissections-respecting-an-atom-plane-split-there`.
  Descending-link connectivity and finite type are not addressed either.
- **Evidence.** For `m = 2`, the bounded exact search of
  `unimodular-cells-synchronize-under-edge-splits` (every stuck `3×3` matrix of entry sum
  at most 36 won) agrees.

## Lesson for general BH

The Serret gate for free-choice subdivisions of lattice-Cantorizations is solvable, and
the proof has a reusable shape.
1. **Generic points.** A reachability tube (half-tube lemma), plus Dirichlet, gives the two
   descent systems a shared vertex.
2. **Shared vertex.** The link at that vertex has rank one lower, so induction applies.
3. **Rational strata.** A point over a proper rational subspace `W` splits into a generic
   problem inside `W` and a full problem in the quotient, both of lower rank. They
   recombine because lifts can be raised by `W`-lattice vectors without moving the point.

No global potential is needed. The pointwise entry-sum potential of Attempt 1 fails
(see Attempt 4 of the claim). What replaces it is the stratification of the point by its
rational hull. This pattern should transfer to any host whose cells are unimodular
simplices: `nV`-type hosts with `GL`-germs, Deligne-type `2V_Λ`, Lagrangian and
train-track split hosts. The remaining finiteness gates there are hierarchy and links,
not synchronization.
