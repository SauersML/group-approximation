---
rg: 2
id: sos-certificates-cannot-see-an-infinite-central-subgroup-proof
kind: route
title: The trace of the quotient algebra forces every square root into (1 - z)R[G]; the central non-zero-divisor Delta_z cancels; augmentation and a spectral argument kill the two natural certificates; compactness of trace-bounded Gram matrices handles fixed-support twisted certificates
target: sos-certificates-cannot-see-an-infinite-central-subgroup
requires:
  - thompson-v-has-haagerup-property
---

Notation is as in the target. Fix a transversal `X ∋ e` of `⟨z⟩` in `G`.

**Step 0 (module structure).** Since `z` is central, `R[G] = ⊕_{x∈X} x·R[z, z^{-1}]` as a
module over the Laurent ring `L = R[z, z^{-1}]`. Write `ξ = Σ_x x f_x` with `f_x ∈ L`.
- `q(ξ) = Σ_x q(x) f_x(1)`, and the `q(x)` are distinct. So `ξ ∈ J` iff every `f_x(1) = 0`. That
  holds iff every `f_x ∈ (1 − z)L`, i.e. iff `ξ ∈ (1 − z)R[G]`.
- `L` is a domain. Multiplication by `Δ_z ∈ L` acts coordinatewise on `(f_x)`, so `Δ_z` is a
  non-zero-divisor in `R[G]`.

**Step 1 (a).** Let `a_i = q(ξ_i) = Σ_w a_{i,w} w` in `R[G/⟨z⟩]`.
- The coefficient of the identity in `a_i* a_i` is `Σ_w a_{i,w}²`.
- `Σ_i a_i* a_i = q(Σ_i ξ_i*ξ_i) = 0`, so `Σ_i Σ_w a_{i,w}² = 0`. Hence every `a_i = 0`.
- By Step 0, `ξ_i = (1 − z)η_i`. Since `z` is central,
  `ξ_i*ξ_i = η_i*(1 − z^{-1})(1 − z)η_i = Δ_z η_i*η_i`. ∎(a)

**Step 2 (b).**
- (⇐) If `p = Σ η_i*η_i`, then `Δ_z^m p = Σ ((1 − z)^m η_i)*((1 − z)^m η_i)`, by centrality.
- (⇒) Induct on `m`. Since `q(Δ_z) = 0`, `Δ_z^m p ∈ J`. So by (a) it equals `Δ_z Σ η_i*η_i`.
  Hence `Δ_z(Δ_z^{m−1}p − Σ η_i*η_i) = 0`, and Step 0 cancels `Δ_z`:
  `Δ_z^{m−1}p ∈ Σ²R[G]`. ∎(b)

**Step 3 (c).** By (b), it is enough to treat `m = 0`.
- *First certificate.* Suppose `Δ_S − λ = Σ η_i*η_i`. Apply the augmentation `ε(g) = 1`, a
  `*`-homomorphism to `R`. The left side gives `−λ < 0`, the right side `Σ ε(η_i)² ≥ 0`.
  This is a contradiction.
- *Second certificate.* Suppose `Δ_S² − λΔ_S ∈ Σ²R[G]` and `S` generates `G`. Let `π` be a
  unitary representation without nonzero invariant vectors, and put `D = π(Δ_S)`.
  - `D = ½ Σ_s π(1 − s)*π(1 − s) ≥ 0`, because `S` is symmetric.
  - `⟨Dv, v⟩ = ½ Σ_s ‖π(s)v − v‖²`, so `ker D` is the space of `π(S)`-invariant vectors. It is
    `0`, since `S` generates.
  - Images of hermitian squares are positive, so `f(D) ≥ 0` for `f(t) = t(t − λ)`. Hence
    `spec D ∩ (0, λ) = ∅`, i.e. `spec D ⊆ {0} ∪ [λ, ∞)`.
  - If `0 ∈ spec D`, it is an isolated point of the spectrum, so its spectral projection is
    nonzero and `0` is an eigenvalue. That was excluded, so `D ≥ λ`.
  - Therefore `max_s ‖π(s)v − v‖² ≥ (2λ/|S|)‖v‖²` for all `v`. So `(S, √(2λ/|S|))` is a
    Kazhdan pair, and `G` has (T). ∎(c)

**Step 4 (d).**
- `T̄ → T̄/⟨z⟩ = T` is onto, and `T ≤ V`, the standard inclusion through binary expansions.
  `V` is Haagerup (`thompson-v-has-haagerup-property`), hence so is `T`.
- An infinite Haagerup group lacks (T): under (T) every cnd function is bounded, so the proper one
  forces finiteness (Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, Thm 2.12.4, as used
  throughout the graph). Property (T) passes to quotients, so `T̄` lacks (T).
- `z` is translation by `1`, which is central of infinite order.
- `T̄` is finitely generated, by lifts of the Cannon–Floyd–Parry generators together with `z`.
- For `C(C,Z) ⋊ V`: it surjects onto `V`, and `1_C` is central of infinite order. It is generated
  by `V ∪ {1_{[0]}}`, because every `1_U`, for `U ≠ ∅, C` clopen, is a `V`-translate of
  `1_{[0]}`, and `1_C = 1_{[0]} + 1_{[1]}`.
- Apply (c) to both groups. ∎(d)

**Step 5 (e).**
- *The twisted algebra.* `I_θ = (z − e(θ))C[G]` is a two-sided `*`-ideal, because
  `(z − e(θ))* = −e(−θ)z^{-1}(z − e(θ))`. By Step 0 over `C`, `A_θ` has basis
  `{σ(x) : x ∈ G/⟨z⟩}`, where `σ(x)` is the transversal element.
  - Write `σ(x)^{-1}σ(y) = σ(x^{-1}y) z^{k(x,y)}`, where the integers `k(x,y)` do not depend on
    `θ`. Then `σ(x)*σ(y) = e(θk(x,y)) σ(x^{-1}y)` in `A_θ`.
  - The functional `τ_θ` (the identity coefficient) satisfies `τ_θ(a*a) = Σ_x |a_x|²`, since
    `x^{-1}y = e` forces `x = y`.
  - Every unitary representation with `π(z) = e(θ)` factors through `A_θ`. So an identity
    `Δ_S − λ = Σ ξ_i*ξ_i` in `A_θ` gives `π(Δ_S) ≥ λ`.
- *The linear system.* For `ξ_i ∈ span σ(F)`, put `P = Σ_i \bar ξ_i ξ_i^T`, a positive
  semidefinite Hermitian `F × F` matrix. The identity reads
  `Σ_{x,y∈F, x^{-1}y=w} P_{xy} e(θk(x,y)) = (Δ_S)_w(θ) − λ[w = e]`
  for every `w ∈ G/⟨z⟩`.
  - The right side is `(Δ_S)_w(θ) = |S|[w = e] − Σ_{s∈S, [s]=w} e(θ j_s)`, where
    `s = σ([s])z^{j_s}`. It is continuous in `θ`.
  - Taking `w = e` gives `tr P = τ_θ(Δ_S) − λ ≤ 2|S| − λ`. So `λ ≤ 2|S|` and `tr P ≤ 2|S|`.
- *Compactness.* Suppose `θ_n → 0` with certificates `(P_n, λ_n)` and `λ_n ≥ λ_0 > 0`.
  - These data are bounded, so a subsequence converges to `(P, λ)` with `P ≥ 0`, `λ ≥ λ_0`.
  - The equations pass to the limit at `θ = 0`, where `A_0 = C[G/⟨z⟩]`. Factor
    `P = Σ_i \bar v_i v_i^T`. This gives `Δ_S − λ = Σ_i ξ_i*ξ_i` in `C[G/⟨z⟩]`.
  - The trivial character sends this to `−λ = Σ_i |ε(ξ_i)|² ≥ 0`, a contradiction.
  - Hence `limsup_{θ→0} Λ_F(θ) ≤ 0`. ∎(e)

**Remark (ε-perturbed certificates).** Suppose
`Δ_z(Δ_S − λ) + ε_n ∈ Σ²R[G]` with Gram matrices over one fixed finite `F ⊆ G`, and
`ε_n → 0`.
- The trace bound `tr P_n = (Δ_z(Δ_S − λ))_e + ε_n` keeps them bounded.
- A limit is then an exact certificate `Δ_z(Δ_S − λ) ∈ Σ²R[G]`, which (c) excludes.
- So such certificates need supports that grow as `ε → 0`, as stated in the target.

**Scope.** Nothing here decides `lifted-thompson-t-center-has-relative-t`. The statements are
limits on a proof technique.
