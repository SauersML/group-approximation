---
rg: 2
id: path-algebra-stable-half-universality-proof
kind: route
title: Run the fibre-product Kazhdan head bound for an arbitrary finitely generated ideal, cut to the fixed space, pad trivially, and read off coverage and the polynomial retract
target: path-algebra-stable-half-is-universal-char-two-stability
requires:
  - ejz-elementary-groups-explicit-kazhdan-constant
  - hyperlinear-flexibly-hs-stable-group-is-residually-finite
  - flexible-hs-stability-descends-to-retracts-finite-index
---

Norms `||·||_(2,n)` are normalized by `n`, and `||·||_HS` is unnormalized. `P_n` is the coordinate
co-isometry onto the first `d_n` coordinates. Notation is that of the claim:
- `R_+ = F_2 Q`, `Γ = E_20(R_+)`;
- `J` is generated as a two-sided ideal by `a_1, ..., a_m`;
- `A = R_+/J`, `π : Γ ->> Γ_J = Γ / E_20(R_+, J)`;
- `F_J = {x_ij(a_k) : i != j, k <= m}`.

## Step 1. Fibre-product ring and its Kazhdan constant

- Put `D = {(x, y) in R_+ x R_+ : x - y in J}`, with coordinate projections `p_1, p_2`.
- `(x, y) = (y, y) + (x - y, 0)`, so `D = Δ(R_+) + (J x 0)`.
- `(r, r)(a_k, 0)(r', r') = (r a_k r', 0)`. So `D` is generated as a unital ring by:
  - the diagonal images of the five generators `e, α, β, γ, δ` of `R_+`;
  - the `m` elements `(a_k, 0)`.
- By `ejz-elementary-groups-explicit-kazhdan-constant`, `E_20(D)` has Kazhdan constant at least
  `κ_m = 1/(8(12√(2(5+m)) + 2√60 + 36√2))`. This is for the generating set `S` of elementary
  matrices over `1` and these `5 + m` generators. The constant depends only on `m`.

**Relative subgroup.**
- `p_2` has the section `Δ`. So `ker(p_2 : E_20(D) -> E_20(R_+))` is the normal closure of
  `{x_ij((a, 0)) : a in J}`.
- This is where the section is used. Write `g in ker p_2` as a word in the `x_ij((r, r))` and the
  `x_ij((a, 0))`. Conjugate every factor of the second kind to the end, and apply `Δ ∘ p_2 = id` to
  the product of the diagonal factors.
- Hence `p_1(ker p_2)` is the normal closure in `Γ` of `{x_ij(a) : a in J}`, which is
  `E_20(R_+, J)`.

## Step 2. Head bound

Let `λ : Γ -> U(V)`, `dim V = d`, with `max_(x in F_J) ||λ(x) - 1||_2 <= δ`.

- **Representation.** `E_20(D)` acts unitarily on `End(V)`, with the normalized HS inner product, by
  `σ(g)T = λ(p_1 g) T λ(p_2 g)^(-1)`.
- **Almost-invariant vector.** For `ξ = 1_V` (norm 1):
  - `x_ij((r, r))` fixes `ξ` exactly.
  - `σ(x_ij((a_k, 0)))ξ = λ(x_ij(a_k))`, which is within `δ` of `ξ`.
  - The remaining generators, the diagonal ones with `r = 1`, also fix `ξ`.
- **Projection.** By the definition of the Kazhdan constant, applied to the component of `ξ`
  orthogonal to the invariants, the projection `T` of `ξ` onto the `σ`-invariant vectors satisfies
  `||T - 1_V||_2 <= δ/κ_m`.
- **Fixed range.** For `g in ker p_2`, invariance reads `λ(p_1 g)T = T`. So
  `range(T) ⊆ W := V^(E_20(R_+, J))`.
- **Codimension.** `T - 1_V` is `-1` on `ker T ⊇ W^⊥`. So
  `codim W <= ||T - 1_V||_HS^2 = d ||T - 1_V||_2^2 <= (δ/κ_m)^2 d`.
- **Invariance.** `W` is `Γ`-invariant, because `E_20(R_+, J)` is normal.

## Step 3. Transfer (item 1)

Let `σ_n : Γ_J -> U(d_n)` be an asymptotic representation.

- **Pull back and round.** `σ_n ∘ π` is an asymptotic representation of `Γ`. By stability there are
  genuine `λ_n : Γ -> U(D_n)`, with `D_n/d_n -> 1`, such that
  `||σ_n(π g) - P_n λ_n(g) P_n*||_(2,d_n) -> 0` for every `g`.
- **Almost trivial on `F_J`.** For `x in F_J`, `π x = 1`, and `σ_n(1) -> 1`. So
  `||P_n λ_n(x) P_n* - 1||_(2,d_n) -> 0`.
  - The compression lemma (Step 5 of wave 22's cone-half proof, reproved below) gives
    `δ_n := max_(F_J) ||λ_n(x) - 1||_(2,D_n) -> 0`.
- **Cut to the fixed space.** Let `W_n = V_n^(E_20(R_+, J))`. By Step 2, `codim W_n <= (δ_n/κ_m)^2 D_n`.
- **Pad trivially.** Define `λ'_n = λ_n|_(W_n) ⊕ 1_(W_n^⊥)`.
  - This is a genuine representation of `Γ`, since `W_n` and `W_n^⊥` are invariant.
  - It kills `E_20(R_+, J)`, so it factors as `λ'_n = μ_n ∘ π` with `μ_n : Γ_J -> U(D_n)`.
- **Estimate.** `λ'_n(g) - λ_n(g)` vanishes on `W_n` and has norm at most 2 on `W_n^⊥`. So
  ```text
  ||λ'_n(g) - λ_n(g)||_(2,D_n) <= 2 sqrt(codim W_n / D_n) <= 2 δ_n/κ_m -> 0,
  ||P_n (λ'_n(g) - λ_n(g)) P_n*||_(2,d_n) <= sqrt(D_n/d_n) · 2δ_n/κ_m -> 0.
  ```
- **Conclusion.** `||σ_n(h) - P_n μ_n(h) P_n*||_(2,d_n) -> 0` for every `h = π g` in `Γ_J`. So `Γ_J`
  is flexibly HS-stable.

**Compression lemma.** Let `λ` be unitary on `C^D`, `d <= D`, `D/d -> 1`, and
`||P λ P* - 1_d||_(2,d) -> 0`. Then `||λ - 1||_(2,D) -> 0`.
- Let `B = λP*`, an isometry. Then
  `||(1 - P*P)B||_HS^2 = d - ||PB||_HS^2 = o(d)`, because `||PB||_HS >= √d - ||PB - 1_d||_HS`.
- So `||(λ - 1)P*||_HS^2 = ||PλP* - 1||_HS^2 + ||(1 - P*P)λP*||_HS^2 = o(d)`.
- On the complement of `range P*`, of dimension `D - d = o(d)`, the HS norm of `λ - 1` is at most
  `2√(D - d)`.

## Step 4. Dichotomy (item 2)

- `Γ_J` is finitely generated, as a quotient of `Γ`.
- If it is hyperlinear, then flexible HS-stability and
  `hyperlinear-flexibly-hs-stable-group-is-residually-finite` make it maximally almost periodic,
  hence residually finite (Malcev).

## Step 5. Coverage (item 3)

**The map.** Let `B = F_2<u, v>/(r_1, ..., r_s)`. Define `ψ : R_+ -> M_2(B)` by
```text
e -> E_11,  f -> E_22,  α -> u E_11,  β -> E_12,  γ -> E_21,  δ -> v E_22.
```

**Well defined.** `R_+` is the free algebra on the quiver. So it suffices that:
- the images of `e, f` are orthogonal idempotents with sum 1;
- each arrow's image is cut by its endpoint idempotents: `E_11 (uE_11) E_11 = uE_11`,
  `E_11 E_12 E_22 = E_12`, and so on.

**Onto.**
- `E_11 M_2(B) E_11 = B E_11` is generated by `ψ(α) = uE_11` and `ψ(βδγ) = E_12 vE_22 E_21 = vE_11`.
- Together with the matrix units `ψ(e), ψ(f), ψ(β), ψ(γ)`, this generates `M_2(B)`.

**Finitely generated kernel.** `M_2(B)` is finitely presented because `B` is. Choose preimages of
a finite generating set, and apply the recipe of wave 22's Step 3: the kernel is generated by the
elements "generator minus word in preimages" together with the relators evaluated on the
preimages.

**Identification.** `E_20(M_2(B)) = E_40(B)`, under the standard identification
`M_20(M_2(B)) = M_40(B)`. The elementary matrices of the two sides generate the same subgroup,
because `x_ij(bE_kl)` is an elementary matrix of size 40 and conversely.

**General `C`.** If `C` is finitely presented, then `M_k(C)` is finitely presented. For large `k` it
is 2-generated, by the classical fact used in wave 22's Step 2. So `B = M_k(C)` gives
`E_40(M_k(C)) = E_(40k)(C)`.

## Step 6. Retract (item 4)

**Retraction.** Let `ρ : R_+ -> F_2[t]` be given by
```text
e -> 1,  f -> 0,  α -> t,  β, γ, δ -> 0.
```
- Orthogonal idempotents go to orthogonal idempotents with sum 1.
- Arrow images are cut correctly: `β = eβf` goes to `1·0·0 = 0`, and so on.

**Section.** Let `ι : F_2[t] -> R_+` send `t -> α + δ`. This is unital, and `ρ ι (t) = t`.

**Consequence.**
- Applying `E_20`, `SL_20(F_2[t]) = E_20(F_2[t])` (Euclidean ring) is a retract of `Γ`.
- `flexible-hs-stability-descends-to-retracts-finite-index` (item 1) makes it flexibly
  HS-stable.

## Step 7. Embedded groups (item 5, under (Z))

**Embedding.**
- `G ⊆ C^×` as group elements, and `C` embeds in `A = M_2(M_k(C))` as the scalar corner.
  Concretely, send `c` to the diagonal matrix of size `2k` with `c` in every entry. This is a unital
  embedding.
- So `G ⊆ A^×`, and `g -> diag(g, 1, ..., 1)` is an injective homomorphism `G -> GL_20(A)`.
- `G` is perfect. For `a, b in A^×`, Whitehead's lemma puts `diag([a,b], 1)` in `E_2(A)`. So the
  image lies in `E_20(A)`.

**Lift.**
- Under `(Z)`, `St_20(A) -> E_20(A)` restricted over `G` is a central extension of `G` by an
  abelian group `K`.
- `H_1(G) = H_2(G) = 0`, so the universal coefficient theorem gives `H^2(G, K) = 0`, and the
  extension splits.
- The splitting `s : G -> St_20(A)`, composed with `St_20(A) ->> Γ_J ->> E_20(A)`, is the injective
  embedding. So `G` embeds in `Γ_J`.

**Conclusion.**
- If `G` is not residually finite, then neither is `Γ_J`, and Step 4 makes `Γ_J` non-hyperlinear.
- **Example: Thompson's group `V`.** It is finitely presented, simple, infinite, hence not
  residually finite. It is acyclic (Szymik–Wahl), so superperfect.

## Checks

- **Consistency with wave 22.** For `J = ker φ` (the Leavitt kernel), Step 3 plus simplicity of
  `Delta` recovers wave 22's item 6. Here `Γ_J` is a quotient of `St_20(R) = Delta` that surjects
  onto `E_20(R) = Delta`, so `Γ_J = Delta`. It is infinite, simple and non-residually-finite, so it
  is non-hyperlinear under the stable-half hypothesis.
- **Uniformity.** The head-bound modulus depends only on `m`. It uses no simplicity or finiteness
  property of `A`. That is why the transfer is universal over finitely presented quotient rings.
- **What this does not claim.** No `Γ_J` is shown to be hyperlinear and non-residually-finite, so
  the stable-half hypothesis is not refuted here.
