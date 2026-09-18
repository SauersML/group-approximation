---
rg: 2
id: recognizable-morphism-kakutani-equivalence-proof
kind: route
title: Centered representations are a continuous bijection from a compact set, so block origins form a clopen full transversal on which the block-counting cocycle identifies the two transformation groupoids
target: recognizable-morphisms-give-kakutani-equivalent-z2-groupoids
requires:
  - steinberg-fp-is-a-kakutani-invariant
---

Notation as in the target. The shift convention is `(σ^k x)(p) = x(p + k)`. For `b ∈ B`, write
`(w(b), h(b))` for the shape of `ω(b)`, which has `w(b), h(b) >= 1`.

## Step 0. Block structure

- **Shapes are constant along rows and columns.** For `y ∈ Y` and horizontally adjacent letters, the
  concatenation `ω(u) ⊙^1 ω(v)` is defined, so `h(y(m)) = h(y(m + e_1))`. Similarly
  `w(y(m)) = w(y(m + e_2))`.
- **Cumulative sizes.** Let `W_y: Z → Z` be the cumulative widths, with `W_y(0) = 0` and
  `W_y(i + 1) − W_y(i) = w(y(i, 0))`. Define `H_y` from the heights `h(y(0, j))` in the same way. Put
  `N_y(m) = (W_y(m_1), H_y(m_2))`.
- **The block rectangles tile the plane.** The rectangles
  `Q_y(m) = N_y(m) + [0, w(y(m))) × [0, h(y(m)))` tile `Z^2`, since both `W_y` and `H_y` are strictly
  increasing bijections onto their images, with gaps equal to the sizes.
- **`ω(y)` is well defined.** Applying the morphism rule to finite rectangular subwords makes `ω(y)`, read
  on `Q_y(m)`, equal to `ω(y(m))`.
- **Shift identity.** Hence `σ^(N_y(m)) ω(y) = ω(σ^m y)`, and `N` is a cocycle:
  `N_y(m + m') = N_y(m) + N_(σ^m y)(m')`.
- **Locality.** `N_y(m)` depends only on `y` on the finite set `[0, m_1] × {0} ∪ {0} × [0, m_2]` (with the
  obvious signs), and the letter `ω(y)(p)` depends only on `y` on a finite window. So `ω` is continuous.

## Step 1. The transversal (item 1)

- **Every point has a centered representation.** If `x = σ^k ω(y)`, let `m` be the index with
  `k ∈ Q_y(m)`. Then `x = σ^(k − N_y(m)) ω(σ^m y)`, and this representation is centered.
- **The pieces.** Let `K` be the finite set of all offsets `k` with `0 <= k < (w(b), h(b))` for some `b`.
  For `k ∈ K`, let `C_k` be the set of points whose unique centered representation has offset `k`.
- **Each piece is compact.** `C_k = σ^k ω(Y_k)`, where `Y_k = {y : k < shape(ω(y(0)))}` is clopen in `Y`.
- **So each piece is clopen.** `X = ⊔_(k ∈ K) C_k`, a finite disjoint union of closed sets.
- **The transversal.** `C = C_0 = ω(Y)` is clopen. It meets every orbit, since `σ^(−k) x ∈ C` for
  `x ∈ C_k`.
- **`ω` is a homeomorphism onto `C`.** It is injective because `(0, y)` is the centered representation
  of `ω(y)`. It is continuous on a compact space, hence a homeomorphism onto `C`.

## Step 2. The groupoid isomorphism (item 2)

- **Convention.** `G_X = X × Z^2`, with `s(x, n) = x`, `r(x, n) = σ^n x`, and
  `(σ^n x, n')(x, n) = (x, n + n')`.
- **The map.** Define `Ψ(y, m) = (ω(y), N_y(m))`.
  - `r(Ψ(y, m)) = σ^(N_y(m)) ω(y) = ω(σ^m y) ∈ C`, so `Ψ` lands in `G_X|_C`.
  - `Ψ` is multiplicative by the cocycle identity.
- **Injective.** `ω` is injective, and `m ↦ N_y(m)` is injective.
- **Surjective.** Let `x = ω(y) ∈ C` and `σ^n x ∈ C`. Take `m` with `n ∈ Q_y(m)`. Then
  `σ^n x = σ^(n − N_y(m)) ω(σ^m y)` is centered. By recognizability and `σ^n x ∈ C`, the offset
  `n − N_y(m)` is `0`.
- **Continuity.** `Ψ` is continuous, since `N_y(m)` is locally constant in `y`. `Ψ^(−1)` is continuous
  too: it recovers `m` from `n` and the locally constant functions `W_y`, `H_y` of `y = ω^(−1)(x)`.

## Step 3. Finite presentation and rigidity (items 3–4)

- **Finite presentation.** `LC(Z, k) ⋊ Z^2 = A_k(G_Z)`. The groupoids `G_Y` (unit space `Y`, full) and
  `G_X|_C` (unit space `C`, full and clopen) are isomorphic. So
  `steinberg-fp-is-a-kakutani-invariant`, item 2, gives item 3.
- **Rigidity.** For SFTs, finite presentation of the `Z^2` crossed product is quantum rigidity
  (`sft-crossed-product-fp-iff-quantum-rigid`, as used in item 3(a) of that node).

## Step 4. Finite type passes from `Y` to `X`

Assume `Y` is an SFT with forbidden patterns `F` on `B_r`. Let `Ω` be any SFT containing `X` on which
`ω` is still recognizable with image union `Ω`. By Step 1, the maps `x ↦ [x ∈ C]` and
`x ↦ (ω^(−1)x)|_(B_r)` on `C` are locally constant, so they are read off finite windows of `x`. Then
`X = {x ∈ Ω : for every p with σ^p x ∈ C, (ω^(−1) σ^p x)|_(B_r) ∉ F}`, a finite-type condition inside `Ω`.

- **Why this set is `X`.** Let `x` be in the set, with centered representation `(k, y)`. Every
  `σ^(k + N_y(m)) x` lies in `C`, and its desubstitution is `σ^m y`, so `y` avoids `F` and `y ∈ Y`. The
  converse is clear.

In the Jeandel–Rao chain one takes `Ω = Ω_i`, and this recovers that `X_i` is an SFT. The finite-type
property was not needed for items 1–3.
