---
rg: 2
id: nv-coordinate-coboundary-subgroups-embed-in-lower-rank-proof
kind: route
title: "Untwist the straightened coordinate into the AF gauge skew product of the Cuntz groupoid, slice its finite blocks off as a finite label, and absorb the label into one remaining binary coordinate"
target: nv-coordinate-coboundary-subgroups-embed-in-lower-rank
requires:
  - brin-thompson-torsion-has-clopen-fixed-sets
  - thompson-v-has-haagerup-property
---

Notation as in the target. `σ` is the shift on `C`; `x_[0,a)` is the prefix of length `a`.

## Step 0. Groupoids and full groups

- **Cuntz groupoid.** `G_2 = {(x, k, y) ∈ C × Z × C : σ^a x = σ^b y for some a, b ≥ 0 with
  a - b = k}`, with `s(x,k,y) = y`, `r(x,k,y) = x`, `(x,k,y)(y,k',z) = (x,k+k',z)` and
  canonical cocycle `c(x,k,y) = k`. For finite words `p, q` put
  `Z(p,q) = {(q w, |q| - |p|, p w) : w ∈ C}`. These sets form a basis of compact open
  bisections of a Hausdorff ample topology (the standard Deaconu–Renault topology).
  An arrow of `G_2` is determined by its triple `(x, k, y)`.
- `G_2^m` is the `m`-fold product (`G_2^0` is the one-point groupoid), with basis the brick
  bisections `Z(p,q) = Π_j Z(p_j, q_j)`, `p, q ∈ ({0,1}^*)^m`, and coordinate cocycles `c_j`.
- For an ample groupoid `𝒢` with compact unit space, `[[𝒢]]` is the group of compact open
  bisections `U` with `s(U) = r(U) = 𝒢^(0)`, under `UV = {uv : u ∈ U, v ∈ V, s(u) = r(v)}`.
  We work with bisections throughout, so no effectiveness is needed.
- **Functoriality** (immediate from the definitions):
  - (F1) a topological groupoid isomorphism `𝒢 ≅ ℋ` induces `[[𝒢]] ≅ [[ℋ]]`;
  - (F2) if `𝒦 ⊆ 𝒢` is an open subgroupoid with `𝒦^(0) = 𝒢^(0)`, then `[[𝒦]]` is the
    subgroup of `[[𝒢]]` of bisections contained in `𝒦`;
  - (F3) if `Y' ⊆ Y` are compact open subsets of `𝒢^(0)`, then `U ↦ U ∪ (Y \ Y')` is an
    injective homomorphism `[[𝒢|_(Y')]] -> [[𝒢|_Y]]`.

**Step 0a. `[[G_2^m]] = mV` (m ≥ 1).** For `g ∈ mV` put `U_g = {(g y, c_g(y), y) : y ∈ C^m}`.
On a brick `[p]` where `g` is `p w -> q w`, `U_g` is `Z(p,q)`, so `U_g` is a full compact open
bisection, and `g ↦ U_g` is an injective homomorphism by the cocycle identity. Conversely let
`U ∈ [[G_2^m]]`. It is a finite union of basic bisections `Z(p^j, q^j) ⊆ U`, and the source
bricks `[p^j]` cover `C^m`. Bricks form a semiring, so there is a partition of `C^m` into
bricks `[p^j v]`, each inside some `[p^j]`, and `U` is the prefix replacement
`p^j v w -> q^j v w` on it. This defines an element `g ∈ mV` with `U_g = U`. ∎

(Where pieces coming from different `j` overlap they carry the same arrows, since `U` is a
bisection; the ranges of the pieces partition `C^m` because `r(U) = C^m` and `U` is a
bisection.)

## Step 1. Untwisting the straightened coordinate

The argument is the same for every `i`; write it for `i = 1` and split
`G_2^n = G_2 × G_2^(n-1)`, `γ = (a, b)`. Put `c'_1(γ) = c_1(γ) - h(r γ) + h(s γ)`. Since `h`
is locally constant, `c'_1` is a continuous cocycle, and `𝒦 = ker c'_1` is a clopen
subgroupoid containing the unit space. For `λ ∈ Λ` every arrow `(λ y, c_λ(y), y)` of `U_λ`
has `c_1 = c_{λ,1}(y) = h(λ y) - h(y)`, so `U_λ ⊆ 𝒦`. By (F2), **`Λ ≤ [[𝒦]]`**.

**Skew product.** `A = G_2 ×_c Z` has arrows `(a, m)` (`a ∈ G_2`, `m ∈ Z`) from `(s a, m)`
to `(r a, m + c(a))`, with `(a, m + c(a'))(a', m) = (a a', m)` and the product topology; it
is ample and Hausdorff. Let `ℋ = A × G_2^(n-1)`, with unit space `C × Z × C^(n-1)`.

Let `ι(x) = (x_1, -h(x), x_2, ..., x_n)` and `Γ = ι(C^n)`, a compact open set, and define
`φ : 𝒦 -> ℋ`, `φ(a, b) = ((a, -h(s γ)), b)`.
- *Source and range.* `s φ(γ) = ι(s γ)`. The range is
  `(r a, -h(s γ) + c(a), r b) = ι(r γ)`, because `c(a) = c_1(γ) = h(r γ) - h(s γ)` on `𝒦`.
  So `φ` maps into `ℋ|_Γ`.
- *Bijective.* For an arrow `((a, m), b)` of `ℋ|_Γ`, source in `Γ` forces
  `m = -h(s a, s b)`, and range in `Γ` then forces `c(a) = h(r) - h(s)`, i.e.
  `(a, b) ∈ 𝒦`. So `φ` is a bijection onto `ℋ|_Γ`, and a homeomorphism because `h` is
  locally constant.
- *Multiplicative.* For composable `γ = (a,b)`, `δ = (a',b')` in `𝒦`,
  `-h(s γ) = -h(r δ) = -h(s δ) + c(a')`, so
  `φ(γ) φ(δ) = ((a, -h(s δ) + c(a'))(a', -h(s δ)), b b') = ((a a', -h(s δ)), b b') = φ(γ δ)`.

Let `M = max |h|` and `Y = C × [-M, M] × C^(n-1) ⊇ Γ`, compact open. By (F1) and (F3):
**`Λ ≤ [[𝒦]] ≅ [[ℋ|_Γ]] ↪ [[ℋ|_Y]]`**, and `ℋ|_Y = A_M × G_2^(n-1)` with
`A_M = A|_(C × [-M, M])`.

## Step 2. `A_M` is AF, explicitly

Fix `L ≥ M`. Let `F_L = {(u, m) : -M ≤ m ≤ M, u ∈ {0,1}^(L+m)}`, a finite set, and
`τ_L : C × [-M, M] -> C × F_L`, `τ_L(x, m) = (σ^(L+m) x, (x_[0, L+m), m))`. It is a
homeomorphism with inverse `(w, (u, m)) ↦ (u w, m)`.

Let `E_L ⊆ A_M` consist of the arrows `((x, m - m', y), m')` from `(y, m')` to `(x, m)` with
`σ^(L+m) x = σ^(L+m') y`. (These are arrows of `G_2`, with `a = L+m ≥ 0`, `b = L+m' ≥ 0`.)
- `E_L` is the finite disjoint union, over `(u, m), (v, m') ∈ F_L`, of the basic compact
  open sets `Z(v, u) × {m'}`. So it is compact open, and it is a subgroupoid containing the
  unit space.
- Under `τ_L`, `((u w, m - m', v w), m') ↦ (w; (u, m), (v, m'))` is an isomorphism of
  topological groupoids `E_L ≅ C × pair(F_L)`. Here `C` is a space (trivial groupoid), and
  `pair(F)` has exactly one arrow between any two points of the finite set `F`.
- `E_L ⊆ E_(L+1)`: apply `σ` to both sides of `σ^(L+m) x = σ^(L+m') y`.
- `⋃_L E_L = A_M`. Take an arrow `((x, k, y), m')` of `A_M` with range level
  `m = m' + k ∈ [-M, M]`, and `a, b ≥ 0` with `a - b = k`, `σ^a x = σ^b y`. For
  `L ≥ max(M, a - m)` we have `L + m ≥ a` and `L + m' = L + m - k ≥ b`, so
  `σ^(L+m) x = σ^(L+m-a) σ^a x = σ^(L+m-a) σ^b y = σ^(L+m') y`. This uses that the arrow is
  determined by `(x, k, y)`.

## Step 3. The generators live in one finite block, as a locally constant label

Let `S` be a finite symmetric generating set of `Λ`, and let `V_s ∈ [[A_M × G_2^(n-1)]]` be the
image of `s ∈ S` under Step 1. The open subgroupoids `E_L × G_2^(n-1)` increase with union
`A_M × G_2^(n-1)`, and each `V_s` is compact, so one `L` has `V_s ⊆ E_L × G_2^(n-1)` for all
`s ∈ S`. By (F2) the image of `Λ` lies in `[[E_L × G_2^(n-1)]]`, and by Step 2 and (F1)

  `E_L × G_2^(n-1) ≅ C × 𝒫`, `𝒫 = pair(F_L) × G_2^(n-1)`, with unit space `F_L × C^(n-1)`.

**Slices.** For `U ∈ [[C × 𝒫]]` and `z ∈ C` let `U_z = {p ∈ 𝒫 : (z, p) ∈ U}`. Arrows of
`C × 𝒫` do not move the `C`-coordinate, so `U_z ∈ [[𝒫]]` (open as a slice of an open set,
compact as a closed subset of the compact `U` in a Hausdorff groupoid, full because `U` is),
and `(U U')_z = U_z U'_z`. A compact open `U` is a finite union of products `Z_j × W_j` with
`Z_j ⊆ C` clopen and `W_j ⊆ 𝒫` compact open. So `z ↦ U_z` is constant on the cells of the
finite clopen partition generated by the `Z_j`.

Take a common such partition `Q` of `C` for the finitely many `V_s`. Slices of products are
products of slices, so every element of the image of `Λ` has slices constant on each cell
`q ∈ Q`. Such an element `U` equals `⋃_q q × U_(z_q)` (`z_q ∈ q`), so
`U ↦ (U_(z_q))_(q ∈ Q)` is an injective homomorphism

  **`Λ ↪ ∏_(q ∈ Q) [[𝒫]] = [[Q × 𝒫]] ≤ [[pair(Q) × 𝒫]] = [[pair(Q × F_L) × G_2^(n-1)]]`**,

where `Q` is a finite discrete space, `Q × 𝒫` is an open subgroupoid of `pair(Q) × 𝒫` with the
same unit space (F2), and `pair(Q) × pair(F_L) = pair(Q × F_L)`.

## Step 4. Absorbing a finite label: `[[pair(F) × G_2^m]] ≅ (m)V`

Let `F` be a finite set with `k ≥ 1` elements.
- **m = 0.** `[[pair(F)]]` is the group of permutation graphs, `≅ Sym(F)`, a finite group.
- **m ≥ 1.** Enumerate `F = {f_1, ..., f_k}` and choose a complete prefix code
  `w_1, ..., w_k` in `{0,1}^*` (the empty word if `k = 1`; otherwise
  `0, 10, ..., 1^(k-2)0, 1^(k-1)`). Define `Θ : pair(F) × G_2^m -> G_2^m` by
  `((f_j, f_l), ((x_1, k_1, y_1), b')) ↦ ((w_j x_1, k_1 + |w_j| - |w_l|, w_l y_1), b')`.
  - It is a functor: levels add, `(k_1 + |w_j| - |w_l|) + (k'_1 + |w_l| - |w_p|) =
    k_1 + k'_1 + |w_j| - |w_p|`.
  - It is bijective. Every `X ∈ C` lies in exactly one `[w_j]`. An arrow `(X, K, Y)` of `G_2`
    with `X ∈ [w_j]`, `Y ∈ [w_l]` and `σ^a X = σ^b Y` (`a - b = K`) comes from
    `(σ^|w_j| X, K - |w_j| + |w_l|, σ^|w_l| Y)`: pick `t ≥ 0` with `a + t ≥ |w_j|` and
    `b + t ≥ |w_l|`; then `σ^(a+t-|w_j|)` and `σ^(b+t-|w_l|)` witness it.
  - It is a homeomorphism: it maps the basic set `{(f_j, f_l)} × Z(p, q) × W` onto
    `Z(w_l p, w_j q) × W`.
  So `pair(F) × G_2^m ≅ G_2^m`, and by (F1) and Step 0a, `[[pair(F) × G_2^m]] ≅ mV`.

## Step 5. Conclusion of item 1

By Steps 1–4 with `F = Q × F_L` and `m = n - 1`, `Λ` embeds in `(n-1)V` when `n ≥ 2`, and in
the finite group `Sym(Q × F_L)` when `n = 1`. ∎

## Item 2. `(K_n) ⟺ (K_(n-1)) ∧ (Q_n)`

- `⟹`. `(n-1)V ↪ nV` by `g ↦ g × id_C`, so `(K_n)` gives `(K_(n-1))`. If `Λ ≤ nV` is Kazhdan,
  it is finitely generated (BdlHV Theorem 1.3.1) and, by `(K_n)`, finite. Item 4 ("only if")
  of `brin-thompson-torsion-has-clopen-fixed-sets` gives a continuous `β : C^n -> Z^n` with
  `c_λ = β∘λ - β`; its first coordinate straightens `c_{·,1}|_Λ`. So `(Q_n)` holds.
- `⟸`. Let `Λ ≤ nV` be Kazhdan. It is finitely generated, and by `(Q_n)` some coordinate is a
  continuous coboundary. By item 1, `Λ` is isomorphic to a subgroup of `(n-1)V` (finite if
  `n = 1`). Property (T) is an isomorphism invariant, so `(K_(n-1))` makes `Λ` finite. ∎

## Item 3

If `n` is least with an infinite Kazhdan `Λ ≤ nV` and some coordinate of `Λ` straightened,
item 1 would put `Λ` in `(n-1)V`, contradicting minimality (for `n = 1`, item 1 makes `Λ`
finite). For `2V`, `n = 2` is least because `(K_1)` holds by
`thompson-v-has-haagerup-property`. ∎

## Remarks (not load-bearing)

- The special case `h ≡ 0` (one coordinate slope identically zero) is also covered by
  `nv-subgroups-with-sign-definite-rank-one-slopes-embed-in-v` with `Z_0 = {i}` and singleton
  blocks. The new content is a nonzero continuous `h`: it is absorbed by the level shift `ι`,
  not by a conjugation inside `nV`.
- Only the product structure `G_2^n = G_2 × G_2^(n-1)` and the AF gauge skew product of the
  single factor `G_2` are used. A general AF-by-`Z^k` groupoid has neither, which is why the
  refutation `af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan` of the general
  statement does not touch this one.
