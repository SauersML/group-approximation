---
rg: 2
id: a2-busemann-transplant-rigidity-proof
kind: route
title: Far germ events are sums of sector cylinders at the tile's site; projective-plane uniqueness makes a sector cylinder the germ times a smaller cylinder at each expansion site, so induction on the radius makes the skeleton central; coherence and a canonical sector chain then hand the tiles to the fibre's rigidity
target: a2-busemann-transplants-preserve-quantum-rigidity
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
  - chamber-fixing-building-lattice-elements-translate-horospheres
---

Lane proof (bh-invent-04, 2026-09-18). It is elementary and algebraic. One adversarial referee
PASS (bh-ref-kourovka-a, 09-18); the referee's two fixes are marked below. Notation is that of the
target. `|·|` on an apartment is the hexagonal (graph) norm. On a sector, `|αa + βb| = α + β`.

**Metric convention (referee fix 1).** A site `γ ∈ Γ` is identified with the vertex `γo ∈ V_0`.
Every distance statement below ("within `r` of `v`") is a building distance on `V_0`, while (Q2),
(Q3) and ball sums use the word metric of `Λ = Λ_0 × Γ` (the `ℓ^1` sum of the two word metrics).
Give `Γ` the finite generating set `S_4 = {γ ≠ 1 : d(o, γo) <= 4}`. Then
`d_Γ(γ, γ') <= ⌈d(γo, γ'o)/2⌉ <= d(γo, γ'o)` for `γ ≠ γ'`.
- Take a building geodesic `x_0, …, x_d`. Every vertex is equal or adjacent to a vertex of `V_0`,
  so choose `y_j ∈ V_0` with `d(x_j, y_j) <= 1`, `y_0 = x_0` and `y_d = x_d`.
- The hops `y_0 → y_2 → y_4 → … → y_d` have length `<= 4`. Since `Γ` acts simply transitively on
  `V_0`, each hop is right multiplication by an element of `S_4`.

So a building ball of radius `r` about `γo` lies in the word ball of radius `r` about `γ`. Every
building-distance bound below therefore implies the word-metric bound that (Q2) and the ball sums
need. The rigidity scales `D_s` and `D_Y` are taken in these word metrics.

## Step 0. Items 1 and 2

- **Item 1.** The proof of `busemann-transplants-give-free-sfts-on-building-lattices`, Proof step 2,
  works verbatim with `X_s` in place of `X_Ω^K`. It uses only three facts:
  - the skeleton is an SFT whose points determine `c`, and in case (ii) the phase;
  - the sector positions `p_ℓ` are read off the radius-`K` germ;
  - `Mu ∈ C°`, which drives the coherence of the rules R3.
- **Item 2.** `(λ, γ)` fixes a point over `c` only if `γc = c` and the fibre point is invariant under
  the shift by `(λ, ±M^(-1) τ_c(γ))`. For `γ ≠ 1`, `τ_c(γ) ≠ 0` by
  `chamber-fixing-building-lattice-elements-translate-horospheres`. A point of `P` over `c` has a
  stabiliser inside that of `c`.

## Step 1. The skeleton algebra and sector cylinders

Let `E_(g,a)(λ, γ)` be a `D`-quantum family for `Y^Γ` on a `k`-space `W_0`, with
`D >= max(D_s, K + R_0)`. Here `g` is the skeleton symbol and `a` the tile.
- **Marginals.** `P_g(λ, γ)` and `T_a(λ, γ)` are the marginals. They are commuting partitions of unity
  at each site, with `E_(g,a) = P_g T_a`.
- **Ball sums** (`path-fold-rigidity-transfer-proof`, Setting). A product of marginals prescribing an
  unrealised partial pattern inside one `D`-ball is `0`.
- **Skeleton algebra.** The skeleton rules forbid a change of `g` along `Λ_0`-edges, so ball sums give
  `P_g(λ, γ) = P_g(1, γ)`. The skeleton marginals form a `D`-family for `X_s`, with `D >= D_s`, so
  they commute. They generate a commutative algebra `𝒞`.
- **The representation `ρ`.** By the compactness step cited in `path-fold-rigidity-transfer-proof`,
  Step 1(c), there is a homomorphism `ρ : LC(X_s, k) -> 𝒞` sending each cylinder to the product of its
  marginals.
  - Unrealised patterns have empty cylinders, so their products are `0`.
  - Every identity between clopen subsets of `X_s` holds for their images.
- **Sector cylinders.** For `v ∈ V_0`, `R >= K`, and a sector piece `S` of radius `R` at `v` (in
  case (ii), together with a phase at `v`), put `E_S(v) = ρ(1_{Z_S(v)})`. Here
  `Z_S(v) = {Q(v,c) ∩ B(v,R) = S}`. Let `𝒞_v^R` be the span of these idempotents.
  - (F1) For fixed `v` and `R` the `E_S(v)` are orthogonal and sum to `I`. Cylinders of radius
    `R' <= R` are sums of cylinders of radius `R`.
  - (F2) *Every skeleton marginal at every site lies in `𝒞_v^R` for some `R`.* The partitions
    `{Z_S(v)}_S` refine as `R` grows and separate points, because a sector determines its chamber at
    infinity. So they generate the topology of the compact space `X_s`, and the finitely many clopen
    sets `{skeleton symbol at γ' = g}` are finite unions of cells of one of them.
  - (F3) *`E_S(v)` is a polynomial in skeleton marginals at sites within distance `R` of `v`.* The
    germs at the `V_0`-vertices of `S` reconstruct `S`. Each `y ∈ S` lies in the germ of some
    `u ∈ S ∩ V_0` with `u` behind `y` in the sector, grown out from `v` in steps of size `K`. So
    `Z_S(v)` is a union of cylinders of patterns on `B(v, R)`.

## Step 2. The Determination Lemma

**Lemma.** Let `c ∈ Ω`, `v ∈ V_0`, and `ℓ = sa + tb ∈ L ∩ C°`, so `s, t >= 1`, with `s + t <= K`. Put
`p = p_ℓ(v)` and `R >= K`. Then `Q(v,c) ∩ B(v,R)` is a function, independent of `c`, of
`Q(v,c) ∩ B(v,K)` and `Q(p,c) ∩ B(p, R - min(s,t))`.

*Proof.* Work in an apartment containing `Q(v,c)`, with coordinates `(α, β) ↔ v + αa + βb`, `α, β >= 0`.
The output only needs points with `α + β <= R`. Intermediate points outside `B(v,R)` are computed as
needed.
1. **Inside `Q(p,c)`** (`α >= s`, `β >= t`). A point at distance `<= R` from `v` is at distance
   `<= R - s - t` from `p`, so it is known.
2. **Closed corner** (`α <= s`, `β <= t`). Its points are at distance `<= s + t <= K` from `v`, so
   they are known.
3. **Uniqueness step.** Let `u` be a vertex, and `y_1, y_2` two neighbours of `u` whose directions are
   at distance 2 in `lk(u)`.
   - `lk(u)` is the incidence graph of a projective plane, of girth 6. So there is exactly one vertex
     `y` adjacent to `u` such that `{u, y_1, y}` and `{u, y, y_2}` are chambers.
   - In the apartment, the pairs of directions
     `(−b, a)`, completing `a − b`, and `(−a, b)`, completing `b − a`, are at angle `120°`, so at link
     distance 2.
4. **Row strip** (`β < t`, `α > s`). Fill rows `β = t−1, …, 0` from left to right, starting from
   `(s, β)` in the corner. The vertex `(α+1, β)` is the completion at `u = (α, β+1)` of
   `y_1 = (α, β)` (direction `−b`) and `y_2 = (α+1, β+1)` (direction `a`).
   - Row `β + 1` is known up to `α + 1`. For `β + 1 = t` it lies in `Q(p,c)`.
   - The fill needs row `t` up to `α = R`, i.e. the point `(R, t)`. That point is at distance `R - s`
     from `p`.
5. **Column strip** (`α < s`, `β > t`). The same, transposed:
   - `(α, β+1)` is the completion at `u = (α+1, β)` of `(α, β)` (direction `−a`) and `(α+1, β+1)`
     (direction `b`);
   - columns `α = s−1, …, 0` are filled bottom-up from `(α, t)` in the corner;
   - the fill needs column `s` up to `β = R`, at distance `R - t` from `p`.

Every point of `Q(v,c) ∩ B(v,R)` is covered by 1, 2, 4 or 5, using `Q(p,c)` only within radius
`max(R − s, R − t) = R − min(s,t)`. ∎

**Operator form.** Fix a skeleton symbol `g` at `v` and `u` with `(w, u) ∈ W`. Let
`p_u = p_{Mu}(v)`, which is read off `g`. For every `S` with germ `g`, and in case (ii) phase `φ`:

```text
E_S(v) = P_g(v) · X_{S,u},     X_{S,u} = Σ_{S' ↦ S} E_{S'}(p_u) ∈ 𝒞_{p_u}^{R-1}.
```

- The sum runs over the pieces `S'` of radius `R − min(s,t) <= R − 1` at `p_u` that, together with
  `g`, produce `S`. In case (ii), the phase at `p_u` is the one `g` and `φ` read off.
- This is `ρ` of an identity of clopen sets, by the Lemma. A piece `S'` that is incompatible with `g`
  gives an empty set.

## Step 3. One-step determinism

For every `λ, v, g, a`,

```text
P_g(v) T_a(λ, v) = P_g(v) Φ^a_g(λ, v),      Φ^a_g(λ, v) = Σ_{π : G(π) = a} ∏_{(w,u) ∈ W} T_{π(w,u)}(λw, p_{Mu}(v)),
```

and all factors commute. Every site involved is within `K + R_0 <= D` of `(λ, v)`. The proof is
ball sums on rule R3, as in Step 2 of `path-fold-rigidity-transfer-proof`. Consequently
`T_a P_g = P_g T_a = P_g Φ = Φ P_g` at `(λ, v)`.

## Step 4. Cylinder induction: the skeleton is central

**Claim(R).** For all `λ, v, a` and every sector cylinder `S` of radius `R` at `v`,
`E_S(v)` commutes with `T_a(λ, v)`.

- **Base, `R <= 2D`.** By (F3), `E_S(v)` is a polynomial in marginals within distance `R <= 2D` of
  `(λ, v)`, so Q2 applies.
- **Step, Claim(R−1) ⇒ Claim(R).** Let `g` be the germ of `S`.
  1. For each factor `T' = T_b(λw, p_u)` of `Φ^a_g(λ, v)`:

     ```text
     E_S T' = P_g X_{S,u} T' = P_g T' X_{S,u} = T' P_g X_{S,u} = T' E_S.
     ```

     The second equality is Claim(R−1) at `(λw, p_u)`. The third is Q2, since `p_u` is within `D`.
  2. So `E_S` commutes with `Φ^a_g(λ, v)`.
  3. By Step 3 and `E_S ⊑ P_g(v)`:
     - `E_S T_a(λ,v) = E_S P_g T_a = E_S P_g Φ = E_S Φ`;
     - `T_a(λ,v) E_S = T_a P_g E_S = Φ P_g E_S = Φ E_S`.

     These are equal.
- **Conclusion.** By (F2), every skeleton marginal lies in some `𝒞_v^R`, so it commutes with every
  `T_a(λ, v)`. Skeleton marginals commute with each other (Step 1). So the skeleton marginals are
  central in the algebra generated by the family, which is item 3.

The induction never commutes operators at distance more than `D`. All far information is carried by
cylinders at the tile's own site, and the Lemma hands it forward to the expansion sites.

## Step 5. Atoms and coherence

- **Atoms.** For a finite set `F` of sites and a skeleton pattern `π` on `F` realised in `X_s`, put
  `Π_π = ρ(1_{[π]})`. These are central (Step 4), pairwise orthogonal, and sum to `I`. A realised `π`
  fixes every classical datum computed inside `F`: sector positions, Busemann differences, merges.
- **Coherence.** Suppose that, under a realised `π`:
  - `b(v) = b(v')`;
  - for some `k`, every `k`-fold expansion site `p_{M(u_1 + … + u_k)}(v)` equals the corresponding
    site of `v'`, with all positions of depth `<= k` computed inside `F`.

  Then `Π_π T_a(λ, v) = Π_π T_a(λ, v')` for all `λ, a`.
  - *Proof by induction on `k`.* By Step 3 and `Π_π ⊑ P_g(v)`,
    `Π_π T_a(λ, v) = Σ_{G(π') = a} ∏ Π_π T_{π'(w,u)}(λw, p_{Mu}(v))`, since `Π_π` is a central
    idempotent.
  - The sites `p_{Mu}(v)` and `p_{Mu}(v')` have equal Busemann vectors and merge after `k − 1`
    further steps. Apply the induction hypothesis term by term.

## Step 6. The section family on a canonical sector chain

- **The canonical chain.** Fix a total order on `V_0`. Put `o_0 = o`, and let `o_{−m−1}` be the least
  `o' ∈ V_0` at distance `|w_0|` from `o_{−m}` with `p_{w_0}(o') = o_{−m}`.
  - This condition is read off the germ at `o'`, since `K >= |w_0|`.
  - Such an `o'` exists: take `o_{−m} − w_0` in an apartment containing `Q(o_{−m}, c)`.
  - The sectors `Q(o_{−m}, c)` increase with `m`.
- **The flat map.** Put `ℓ(z) = p_{Mz + m w_0}(o_{−m})` for any `m` with `Mz + m w_0 ∈ C̄`. By nesting,
  `p_{ℓ'} ∘ p_{ℓ''} = p_{ℓ' + ℓ''}`, this does not depend on `m`.
  - `b(ℓ(z)) = Mz`.
  - Finitely many `ℓ(z)` lie in one sector `Q(o_{−m}, c)`, where
    `d(ℓ(z), ℓ(z')) = |M(z − z')| <= μ |z − z'|_1`, with `μ = max_i |Me_i|`.
- **Coefficients.** `c_{z,v} = ρ(1{ℓ(z) = v})` is a finite sum of atoms. For fixed `z`, these are
  orthogonal, central, finitely many are nonzero, and they sum to `I`.
- **The family.** Define

```text
F_a(λ, z) = Σ_v c_{z,v} T_a(λ, v).
```

  - **(Q1).** Holds because the coefficients are orthogonal central idempotents summing to `I`.
  - **(Q2).** Suppose `d((λ,z), (λ',z')) <= 2D_Y`. The surviving terms pair sites at distance
    `<= 2μ D_Y <= 2D`.
  - **The base shift (referee fix 2).** The Setting does not assume `M(N^2) ⊆ C̄`. So fix
    `u_* ∈ Z^2` with `M u_* ∈ C°`; any `u` with `(w, u) ∈ W` will do. Let `N_0` be the least `N >= 0`
    with `M f + N M u_* ∈ C̄` for every `f ∈ Z^2` with `|f|_1 <= D_Y`. It exists because `C°` is
    an open cone containing `M u_*` and `|M f| <= μ D_Y`. Put
    `κ = μ D_Y + N_0 |M u_*|`, which bounds the norm of every such offset.
    - When `M(N^2) ⊆ C̄`, as in the NE example of the target and for the `M` of
      `busemann-transplants-give-free-sfts-on-building-lattices`, take `u_* = 𝟏` and `N_0 <= D_Y`.
      Then `κ <= 3μ D_Y`, which recovers the original constant.
  - **(Q3).** Let `α` be a pattern on `(λ_p, z_p) B_{D_Y}` that does not occur in `Y`, and put
    `z_* = z_p − N_0 u_*`.
    - Multiply each term `e ∏_f T_{α(f)}(λ_p f_0, v_f)` of the product by
      `Σ_{v_*} c_{z_*, v_*} = I`.
    - Where `e c_{z_*,v_*} ≠ 0`, the ball sits at the offsets `M f_z + N_0 M u_* ∈ C̄`, of norm
      `<= κ`, in `Q(v_*, c)`. Here `v_f = p_{M f_z + N_0 M u_*}(v_*)` by nesting. So
      `e c_{z_*,v_*} ⊑ e'`, where `e'` is `ρ` of the event "these offsets from `v_*` land at the
      `v_f`". By (F3) that event is a polynomial in skeleton marginals within `κ` of `v_*`.
    - `e' ∏ T` expands into unrealised partial patterns inside a ball of radius `κ + D_Y <= D`,
      since a realising point's fibre would contain `α`.
    - So `e' ∏ T = 0` by ball sums, and each term vanishes.

  Hence `F` is a `D_Y`-quantum family for `Y`. All `F_a(λ, z)` commute.

## Step 7. Conclusion

- **Letters as combinations of `F`.** Fix `v`. For each skeleton point there are:
  - a unique `z` with `b(v) = Mz`;
  - a unique `v'' = ℓ(z)`;
  - a finite merge depth of `v` and `v''`. Sectors toward one chamber share a subsector, and equal
    Busemann vectors make the expansion sites meet there, as in
    `busemann-transplants-give-free-sfts-on-building-lattices`, Proof step 2.

  These are clopen conditions. By compactness, one finite `F` decides them on every atom `Π_π`. By
  Step 5, `Π_π T_a(λ, v) = Π_π T_a(λ, ℓ(z_π)) = Π_π F_a(λ, z_π)`, so

```text
T_a(λ, v) = Σ_z ρ(1{b(v) = Mz}) F_a(λ, z).
```

- **Commutation.** Letters are finite combinations, with orthogonal central coefficients, of pairwise
  commuting `F`'s, so they commute. The skeleton is central, and `E_(g,a) = P_g T_a`. So the family
  commutes, and `Y^Γ` is `D`-quantum rigid for `D >= max(D_s, K + R_0, κ + D_Y)`, with `κ`
  from Step 6. When `M(N^2) ⊆ C̄`, `κ + D_Y <= (3μ + 1) D_Y`.
- **The converse** is the fold lemma. The map `(λ, γ) ↦ (λ, M^(-1) b_c(γo))` along one skeleton point is
  onto and Lipschitz. After rescaling the metric of `Z^2` it is 1-Lipschitz, and rigidity at large
  scale does not depend on the metric (`fp-v-times-subshift-full-groups-force-quantum-rigidity`). ∎

## Remarks

- **Products of trees.** The Lemma of Step 2 holds there with rays in place of sectors. A cylinder at
  `x` of radius `R` is the germ at `x` times a cylinder of radius `R − 1` at each expansion site.
  So Step 4 reproves (C) of `tree-product-busemann-transplants-preserve-quantum-rigidity` without
  arrow chains.
- **Other buildings.** Ã2 enters only in Step 2. Any Euclidean building lattice with a rigid SFT
  skeleton satisfies the theorem, provided sector cylinders at `v` are determined by the germ and a
  strictly smaller cylinder at each open-cone expansion site. The natural tool for types C̃2, G̃2 and
  higher rank is uniqueness of short galleries in the spherical links; this was not checked.
- **Where openness of the cone enters.** In Step 2, `s, t >= 1`. With `p` on a wall, `min(s,t) = 0`
  and the radius does not drop, so the induction of Step 4 stalls.
- **Calibration.** A non-deterministic decoration, such as the full `Z^2`-shift, has no Step 3. Its
  transplant is not rigid, by the fold lemma, since the full shift is not.
