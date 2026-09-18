---
rg: 2
id: tree-product-busemann-transplant-rigidity-proof
kind: route
title: Monotone arrow chains make every arrow central (each chain piece freezes the far arrow or lets the tile expansion step closer); central arrows give coherence and a section family on a canonical flat, whose fibre rigidity finishes the proof
target: tree-product-busemann-transplants-preserve-quantum-rigidity
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
---

Lane proof (bh-invent-04, 2026-09-18). It is elementary and algebraic, and it has not been reviewed.
Notation is that of the target. For idempotents, `A ⊑ B` means `AB = BA = A`; it is transitive.

## Step 0. Items 1, 2 and 5

- **Arrows code ends.** The skeleton rules are:
  - on each `T_i`-edge `{γ, γs}` (`s ∈ S_i`), exactly one of "the `i`-arrow at `γ` points to `γs`" and
    "the `i`-arrow at `γs` points to `γ`" holds;
  - for `j ≠ i` and `s ∈ S_j`, the `i`-arrows at `γ` and `γs` point to the same vertex of `T_i`.

  A point satisfying these orients every edge of every `T_i`, with out-degree one at each vertex. So it
  is a tuple of ends `ξ`, read off at any site. Thus (H_Ω) holds.
- **Transplant rules.** The transplant adds:
  - (R3) `t(λ, γ) = G(t(λw, γ[u]))_{(w,u) ∈ W}`, where `γ[u]` is the vertex reached from `γo` by `u_i`
    forward steps in each `T_i`, read off the arrows;
  - (R2) along every forward cone, the tiles avoid the forbidden patterns of `Y`.
- **Item 1.** Sufficiency is the coherence argument of
  `busemann-transplants-give-free-sfts-on-building-lattices`, Proof step 2. The classical form of
  Step 4 below also gives it. Two vertices of `T_i` at the same level have a common forward ancestor,
  and `b_ξ` maps `V` onto `Z^r`.
- **Item 2.**
  - *Fixed points.* `(λ, γ)` fixes `(ξ, y)` iff `γξ = ξ` and `y` is invariant under the shift by
    `(λ, ±τ_ξ(γ))`, with a sign fixed by convention.
  - *Nonzero translation.* Suppose `γ` fixes `ξ` and `τ_ξ(γ) = 0`. Then each coordinate `γ_i` fixes
    `ξ_i`, so it is not an inversion, and preserves `b_i`, so it is not hyperbolic. So `γ_i` is elliptic
    and fixes a ray to `ξ_i` pointwise. Then `γ` fixes a vertex of `V`, and `γ = 1`.
  - *Necessity.* For `F_{n_1} × … × F_{n_r}`, the element `(a_1^{τ_1}, …, a_r^{τ_r})`, with `a_i`
    basis elements, realises every `τ ∈ Z^r` at the ends `a_i^{+∞}`.
- **Item 5.** Fix one skeleton point `ξ`. The map `(λ, γ) ↦ (λ, b_ξ(γo))` is 1-Lipschitz, since each
  generator moves one Busemann coordinate by `±1`. It is onto, and every fold `y ∘ β ⊗ ξ` lies in
  `Y^Γ` by definition.

## Step 1. Marginals, arrow events, ball sums

Let `E_(α,a)(λ, γ)` be a `D`-quantum family for `Y^Γ` on a `k`-space `W_0`, with `D > R_W`. Here
`α = (α_1, …, α_r)` is the arrow tuple and `a ∈ A` the tile.
- **Marginals.** `T_a(λ, γ)` and `P^i_s(λ, γ)` (the `i`-arrow is `s ∈ S_i`) are marginal sums. At
  each site the marginals are commuting partitions of unity, and `E_(α,a) = T_a ∏_i P^i_(α_i)`.
- **Ball sums** (`path-fold-rigidity-transfer-proof`, Setting). A product of marginals prescribing a
  partial pattern inside some `gB_D` that no point of `Y^Γ` realises is `0`.
- **Arrow events.** For a vertex `x ∈ T_i` and a neighbour `x'`, put
  `[x → x'] = P^i_s(λ, γ)` for any site whose `T_i`-coordinate is `x`, where `s` is the label of the
  edge `xx'` there. The constancy rule and ball sums along `S_j`-edges (`j ≠ i`) and `Λ_0`-edges show
  this does not depend on the site. So an arrow event can be placed at any site with `T_i`-coordinate
  `x`, which is at `Λ`-distance `d_i(x, π_i(γ))` from `(λ, γ)`.
- **Edge and chain relations.** The edge rule and ball sums give `[x → x'] + [x' → x] = I`. Let
  `g_0, …, g_m` be a geodesic of `T_i` and `A_j = [g_j → g_{j+1}]`. Since `A_{j+1}` and
  `I - A_j = [g_{j+1} → g_j]` are distinct letters at one site, `A_{j+1} = A_{j+1} A_j = A_j A_{j+1}`.
  So `A_m ⊑ … ⊑ A_0`, and `B_j := I - A_j` satisfy `B_0 ⊑ … ⊑ B_{m-1}`.

## Step 2. One-step determinism

Fix `(λ, γ)`. For an assignment `σ` of arrows along the forward paths of length `<= max u_i` from the
coordinates `π_i(γ)`, let `e_σ` be the product of the corresponding arrow events. Then

```text
e_σ T_a(λ, γ) = e_σ Φ^a_σ(λ, γ),      Φ^a_σ(λ, γ) = Σ_{π : G(π) = a} ∏_{(w,u) ∈ W} T_{π(w,u)}(λw, γ_σ[u]),
```

and all factors commute. Here `γ_σ[u]` is the vertex reached under `σ`. Every site involved lies
within `R_W < D` of `(λ, γ)`.
- **Why it holds.** By R3, the partial pattern "`σ`, tile `a` at `(λ, γ)`, tiles `π` with `G(π) ≠ a`"
  is not realised. Kill it by ball sums, then sum over `π` using `Σ_π ∏ T = I`. This is Step 2 of
  `path-fold-rigidity-transfer-proof`, with a cone in place of a row.

## Step 3. Centrality (C)

Fix `i`. Let `H_i(n)` be the statement:

> for all `x' ∈ T_i`, all neighbours `x''` of `x'`, all sites `(λ, γ)` with `d_i(x', π_i(γ)) <= n`, and
> every marginal `M` at `(λ, γ)` (a tile or an arrow of any tree), `[x' → x'']` commutes with `M`.

**Base, `n <= 2D`.** Place `[x' → x'']` at the site with `Λ_0`-coordinate `λ`, `T_i`-coordinate `x'`
and the other coordinates of `γ`. It is at distance `<= n` from `(λ, γ)`, so (Q2) applies.

**Step, `H_i(n) ⇒ H_i(n+1)` for `n >= 2D`.** Let `d_i(x', π_i(γ)) = n + 1`, with geodesic
`π_i(γ) = g_0, …, g_{n+1} = x'`, and let `A_j`, `B_j` be as in Step 1. Put `P = [x' → x'']` and

```text
Q_{-1} = I - A_0,     Q_j = A_j - A_{j+1}  (0 <= j <= n-1),     Q_n = A_n.
```

- **The pieces.** `Σ_{j=-1}^{n} Q_j = I`. Every `Q_j` involves only arrows at `g_0, …, g_n`, at
  `T_i`-distance `<= n` from `π_i(γ)`. So by `H_i(n)` every `Q_j` commutes with every marginal `M` at
  `(λ, γ)`.
- **The pieces `j < n` freeze the far arrow.** From `A_n ⊑ A_j`:
  - `B_n Q_j = Q_j B_n = Q_j` for `-1 <= j <= n-1`. For example,
    `(I - A_n)(A_j - A_{j+1}) = A_j - A_{j+1} - A_n + A_n`.
  - `B_n = [x' → g_n]`, and the other letters at `x'` are orthogonal to it.
  - So `P Q_j = Q_j P = c Q_j`, with `c = [x'' = g_n]`.
  - Hence `[P, Q_j M] = c Q_j M - Q_j M P = c Q_j M - M Q_j P = 0`.
- **The last piece lets the tile step closer.** `Q_n = A_n ⊑ A_0, …, A_{U-1}` with
  `U = max u_i <= R_W < n`. So under `A_n` the forward path in `T_i` from `g_0` is `g_0 → g_1 → …`.
  - *Tiles.* Sum Step 2 over the assignments `σ'` of the forward paths in the trees `j ≠ i`.
    - Their events commute with `A_n`: arrows of different trees commute, since both can be placed at
      one site.
    - They commute with `T_a(λ, γ)` by Q2: place them at sites that differ from `(λ, γ)` only in
      `T_j`, within distance `U`.
    - Write `e_σ = A_0 ⋯ A_{U-1} e_{σ'}`. Since `A_n = A_n A_0 ⋯ A_{U-1}`, this gives
      `A_n T_a(λ, γ) = Σ_{σ'} A_n e_σ T_a(λ, γ) = Σ_{σ'} A_n e_{σ'} Φ^a_σ(λ, γ)`.
  - `P` commutes with `A_n` (adjacent), and with each `e_{σ'}`. The latter are arrows of other trees:
    place them at `T_i`-coordinate `x'`.
  - `P` also commutes with each tile of `Φ^a_σ`. Their `T_i`-coordinates are `g_{u_i}` with `u_i >= 1`,
    at distance `n + 1 - u_i <= n` from `x'`, so `H_i(n)` applies.
  - **This is where Step 3 uses `u_i >= 1`.** Hence `[P, A_n T_a(λ, γ)] = 0`.
  - *Arrows at `g_0`.* `A_n ⊑ A_0` gives `A_n [g_0 → y] = [y = g_1] A_n`, so `[P, A_n [g_0 → y]] = 0`.
  - *Arrows of other trees at `(λ, γ)`.* These commute with `P` by placement, as above.
- **Conclusion.** `[P, M] = Σ_j [P, Q_j M] = 0`, since each `Q_j` commutes with `M`.

So `H_i(n)` holds for all `n` and all `i`. In particular all arrow events commute: this is
`free-group-boundary-shifts-are-quantum-rigid` again, now over any product lattice. Every arrow event
is central in the algebra generated by the family, which is item 3.

## Step 4. Atoms and coherence

- **Atoms.** Let `F` be a finite set of tree vertices, containing, in each `T_i`, a subtree and all
  its neighbours. For each assignment `σ` of an arrow at every vertex of `F`, let `Π_σ` be the product
  of the corresponding arrow events.
  - These are commuting central idempotents (Step 3), pairwise orthogonal, and they sum to `I`.
  - `Π_σ = 0` unless `σ` obeys the edge rule on `F`. Two adjacent arrows that both point along their
    edge, or both point elsewhere, multiply to `0`. In the second case use
    `[x → y] ⊑ I - [x → x'] = [x' → x]` for `y ≠ x'`.
  - A nonzero `Π_σ` therefore fixes, exactly as an end does, the forward paths inside `F`, the levels
    `b_i` of the vertices of `F` (normalised at `o`), and the forward ancestors inside `F`.
- **Coherence.** Let `Π = Π_σ ≠ 0`. Let `γ, γ'` have equal Busemann vectors under `σ` and common
  forward ancestors `f_σ^k(π_i(γ)) = f_σ^k(π_i(γ'))` after `k` steps in every tree, all inside `F`.
  Then for every `λ` and `a`,

```text
Π T_a(λ, γ) = Π T_a(λ, γ').
```

  - *Induction on `k`.* The case `k = 0` is trivial.
  - For `k >= 1`, Step 2 under `Π ⊑ e_σ` gives `Π T_a(λ, γ) = Σ_{G(π) = a} ∏ Π T_{π(w,u)}(λw, γ_σ[u])`.
    `Π` is a central idempotent, so it distributes over products.
  - The tree coordinates of `γ_σ[u]` and `γ'_σ[u]` are `f_σ^{u_i}` of those of `γ` and `γ'`. Since
    `u_i >= 1`, they merge after at most `k - 1` further steps.
  - So by induction the two expansions agree term by term.
  - This is Step 4 of `path-fold-rigidity-transfer-proof` in every tree at once.

## Step 5. The section family on a canonical flat

- **The canonical flat.** Fix a total order on the neighbours of every vertex of every `T_i`. Under an
  end, define the canonical line `ℓ_i : Z -> V(T_i)` by:
  - `ℓ_i(0) = π_i(o)`;
  - `ℓ_i(m+1)` is the forward neighbour of `ℓ_i(m)`;
  - `ℓ_i(m-1)` is the least neighbour of `ℓ_i(m)` other than its forward one.

  By the edge rule, the forward neighbour of `ℓ_i(m-1)` is `ℓ_i(m)`. So `ℓ_i` is a geodesic line with
  `b_i(ℓ_i(m)) = m`, along which the arrows run forward. Put `ℓ(z) = (ℓ_1(z_1), …, ℓ_r(z_r)) ∈ V`. On
  this flat the `ℓ^1` metric of `Z^r` is the metric of `V`, and every forward cone of a flat point
  stays in the flat.
- **Coefficients.** For fixed `z`, the events `c_{z,v} = [ℓ(z) = v]` are finite sums of atoms. They
  are orthogonal and central, finitely many are nonzero, and they sum to `I`.
- **The family.** Define

```text
F_a(λ, z) = Σ_v c_{z,v} T_a(λ, v).
```

  - **(Q1).** Holds because the coefficients are orthogonal central idempotents summing to `I`.
  - **(Q2).** Suppose `d((λ, z), (λ', z')) <= 2D_Y`. Only terms with `c_{z,v} c_{z',v'} ≠ 0` survive.
    There `d((λ, v), (λ', v')) = d(λ, λ') + |z - z'|_1 <= 2D_Y <= 2D`.
  - **(Q3).** Let `α` be a pattern on `(λ_p, z_p) B_{D_Y}` that does not occur in `Y`.
    - Expand `∏ F_{α(f)}` into terms `e ∏_f T_{α(f)}(λ_p f_0, v_f)`, with `e` a product of
      coefficients. If `e ≠ 0`, the `v_f` lie in the forward cone of `v_* = ℓ(z_p - D_Y 𝟏)`.
    - Then `e ⊑ e'`, where `e'` is the product of the arrow events along that cone's forward paths
      of length `<= 2D_Y`.
    - The operators of `e' ∏ T` lie within `(2r + 1) D_Y <= D` of `(λ_p, v_*)`. They prescribe
      forward paths from `v_*` carrying the letters of `α` at their Busemann offsets.
    - No point of `Y^Γ` realises this, since its `y` would contain `α`.
    - So `e' ∏ T = 0` by ball sums, and `e ∏ T = e e' ∏ T = 0`.

  Hence `F` is a `D_Y`-quantum family for `Y` on `W_0`. By rigidity of `Y`, all `F_a(λ, z)` commute.

## Step 6. Conclusion

- **Letters are combinations of `F`.** Take a site `(λ, γ)`, and a finite `F` containing the geodesics
  from `π_i(o)` to `π_i(γ)` and enough of each tree around them. On every atom `Π_σ ≠ 0`:
  - `γ` has a Busemann vector `z_σ`, and `γ` and `ℓ(z_σ)` have common forward ancestors inside `F`
    (two vertices of a tree at one level do);
  - so `Π_σ T_a(λ, γ) = Π_σ T_a(λ, ℓ(z_σ)) = Π_σ F_a(λ, z_σ)`, by Step 4.

  Summing over atoms, `T_a(λ, γ) = Σ_z [b(γ) = z] F_a(λ, z)`. This is a finite sum with orthogonal
  central coefficients.
- **Commutation.**
  - Any two letters are such combinations of pairwise commuting `F`'s, so they commute.
  - Arrows are central (Step 3).
  - `E_(α,a) = T_a ∏_i P^i_(α_i)`.

  So the whole family commutes, and `Y^Γ` is `D`-quantum rigid over `k`. This is item 4. ∎

## Remarks

- **Hypotheses used.**
  - Nothing uses `dim W_0` or `char k`.
  - `Γ` enters only through the product-of-trees geometry: chains in each tree, invariance of each
    tree's arrows under moves in the others, and simple transitivity on `V`, which is used for
    freeness.
  - `Y` enters through its cone rule and its rigidity at scale `D_Y`.
- **Where `u_i >= 1` enters.**
  - Step 3, last piece: the expansion must step toward the far arrow in `T_i` whatever the tile does
    in the other trees.
  - Step 4: the expansions must merge in every tree.

  With `u_i = 0` allowed, as for an unsheared NE rule over `T_1 × T_2`, Step 3 fails. The
  `T_2`-coordinate of `t(f(x_1), x_2)` does not move. This is the operator form of the "open cone"
  condition of `busemann-transplants-give-free-sfts-on-building-lattices`.
- **Single-free-branch calibration** (`quantum-rigid-sfts-over-products-have-a-single-free-branch`).
  Passes. A slab across a `T_i`-cut fixes the fibre on its forward side. Extensions vary only in the
  branch containing `ξ_i`.
