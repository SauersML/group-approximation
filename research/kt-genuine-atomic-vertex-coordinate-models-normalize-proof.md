---
rg: 2
id: kt-genuine-atomic-vertex-coordinate-models-normalize-proof
kind: route
title: Conjugate the atomic vertex coordinates to genuine matrix representations, tensor away the trace, and run the rounding chain at zero error
target: kt-genuine-atomic-vertex-coordinate-models-normalize
requires:
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - nonunit-projection-bounded-by-root-spectral-mass
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - vertex-rounding-deep-nonunit-root-mass-vanishes
  - kazhdan-images-in-haagerup-algebras-are-atomic
artifacts:
  - research/artifacts/kt-ii1-coordinate-model-transfer-2026-09-16.md
---

Notation as in the target. For a homomorphism `σ : G -> U(M)` put `R_σ = σ(Γ)' ∩ M` and
`K_σ = {g : [σ(g), R_σ] = 0}`, and let `N = <<Γ>>_G`. The artifact carries full proofs of every step
below except the premises, which are used as black boxes.

1. **Criterion and transport** (artifact §0).
   - `σ(G)` normalizes `R_σ` iff `N <= K_σ`.
   - Let `Φ` be an injective unital `*`-homomorphism of ambients with `Φ ∘ σ = σ'`. Then `Φ` maps
     witnesses of non-commutation to witnesses, so `K_(σ') <= K_σ`.
2. **Separable coordinates** (Theorem T, Step 1).
   - Fix witnesses `p_g in R_σ` for `g notin K_σ`, unitary lifts `σ_i(g)` with `σ_i|Γ = ρ_i`, and
     bounded lifts `p_(g,i)`.
   - The von Neumann algebras `N_i` they generate are separable, Connes-embeddable and contain
     `A_i = ρ_i(Γ)''`.
   - Replacing `M` by `prod_ω N_i` does not enlarge the stabilizer.
3. **Matrix coordinates, genuine on the vertex** (Lemmas 1.2–1.4, Step 2).
   - Embed `N_i` trace-preservingly into a matrix ultraproduct `Q_i = prod_(V_i) M_(d_i(x))`, through
     `R^ω` and the conditional expectations of `R`.
   - An atomic `A_i = directSum M_(k_l)` with trace weights `w_l` has a second embedding `ι_i`:
     `a -> directSum_(l <= L(x)) a_l (tensor) 1_(floor(w_l d)) (+) 0`. Padding by the trivial
     representation makes `ι_i ∘ ρ_i` genuine coordinatewise.
   - Unital trace-preserving embeddings of an atomic algebra into a matrix ultraproduct are unitarily
     conjugate, since equal-trace projections are equivalent. After conjugation, the vertex
     coordinates are genuine representations `Γ -> U(d_i(x))`.
4. **One ultraproduct** (Lemma 1.1, Step 3). The iterated ultrafilter gives an injective
   trace-preserving `J : prod_ω Q_i -> prod_W M_d`. The image model has genuine vertex coordinates
   and a smaller stabilizer.
5. **Trace and indexing** (Lemmas 1.5, 1.6, 3.1).
   - `G` is residually finite, by reduction of exponents modulo `m`.
   - Tensoring with ultraproducts of regular representations of the finite quotients `G/G_j` makes
     the model trace-preserving. It keeps vertex coordinates genuine, and `p (tensor) 1` keeps the
     witnesses.
   - Amplifying coordinates to make the dimension injective and pushing the ultrafilter forward gives
     `σ♭ : G -> U(prod_U M_n)`. It is trace-preserving, has genuine `π_n : Γ -> U(n)` for every `n`,
     and satisfies `K_(σ♭) <= K_σ`.
6. **The chain** (Theorem N). Choose coordinates with `σ_n|Γ = π_n`. Then (H1) holds with zero error
   and no padding.
   - Item 1 of the first premise: `π_n` factors through `St_r(A_u × A_nu)`, which defines `P_n`.
   - The second premise: `τ(1 - P_n) <= r(r-1)[μ_n(depth_nu = 1) + μ_n(depth_nu > 1)]`.
   - Item 5 of the third premise and the fourth premise send both terms to `0` along `U`.
   - Item 4 of the first premise: `σ♭(G)` normalizes `R_(σ♭)`.
   - So `N <= K_(σ♭) <= K_σ`, and step 1 proves item 1 of the target.
7. **Haagerup case.** `Γ` has property (T). The fifth premise makes a Haagerup `ρ_i(Γ)''` atomic, and
   records that amenable coordinates, and those with separable predual and the Haagerup property,
   qualify. This proves item 2.
