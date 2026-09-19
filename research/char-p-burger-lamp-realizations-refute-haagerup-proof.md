---
rg: 2
id: char-p-burger-lamp-realizations-refute-haagerup-proof
kind: route
title: "Lamp embedding, duality, a spectral transfer of relative (T) through a quotient, a finite central projection and Schoenberg; the baker map gives the torus lift"
target: char-p-burger-lamp-realizations-refute-haagerup
requires:
  - elementary-linear-semidir-pair-relative-t
---

Notation as in the target. Throughout, `R` is a finitely generated infinite commutative unital
`F_p`-algebra, `M = R^2`, and `M^ = Hom(M, F_p)`. For `u ∈ F_p` write `e(u) = exp(2πi u/p)`.

**Relative (T), as used.** A pair `(G, H)` of a countable group and a subgroup has relative (T) if
there are a finite `Q ⊆ G` and `ε > 0` with the following property. Every unitary representation
with a unit vector `ξ` satisfying `‖π(s)ξ − ξ‖ < ε` for all `s ∈ Q` has a nonzero `H`-invariant
vector. This is the form stated in `elementary-linear-semidir-pair-relative-t`.

## Step 1 (lamp lemma): `C(C^n, F_p) ⋊ nV ≤ nV`

Here `C(C^n, F_p)` is the additive group of locally constant maps, with `nV` acting by
`(g·f)(x) = f(g^-1 x)`.

- **Bricks.** Choose a complete prefix code `u_0, ..., u_(p-1)` in `{0,1}^*`: `u_a = 1^a 0` for
  `a < p−1`, and `u_(p-1) = 1^(p-1)`. Let `β_a(x_1, x_2, ..., x_n) = (u_a x_1, x_2, ..., x_n)`.
  The bricks `B_a = β_a(C^n)` partition `C^n`. Index them by `a ∈ F_p`.
- **Lifts.** For `g ∈ nV` and `f ∈ C(C^n, F_p)` define
  `ĝ(β_a x) = β_a(g x)` and `f̂(β_a x) = β_(a + f(x))(x)`.
- **They lie in nV.**
  - `ĝ` is `g` conjugated by `β_a` on each brick. So it is a prefix replacement on the boxes
    `β_a(box)`.
  - Refine a dyadic box partition until `f` is constant on each box `D`. Then `f̂` maps `β_a(D)` to
    `β_(a+f(D))(D)` by replacing the prefix `u_a` with `u_(a+f(D))`.
  - Both maps are bijections, with inverses `(g^-1)^` and `(−f)^`.
- **Relations.**
  - `(f_1 + f_2)^ = f̂_1 f̂_2`, and `(g_1 g_2)^ = ĝ_1 ĝ_2`.
  - `ĝ f̂ ĝ^-1 (β_a x) = ĝ f̂ (β_a g^-1 x) = ĝ β_(a + f(g^-1 x))(g^-1 x) = β_(a + f(g^-1 x))(x)`,
    which is `(g·f)^(β_a x)`.
  - So `(f, g) ↦ f̂ ĝ` is a homomorphism from `C(C^n, F_p) ⋊ nV`.
- **Faithful.** If `f̂ ĝ = id`, then `β_(a + f(gx))(g x) = β_a x` for all `a, x`. So `g x = x` and
  `f = 0`.

## Step 2 (duality): an invariant module in the lamp group

Let `Λ = ⟨g_1, ..., g_k⟩ ≤ nV`.

- **The affine action is well defined.** Every word `w` in the `g_i^±1` gives a composite affine
  map `a_w` with `φ∘w = a_w∘φ`.
  - Suppose two words `w` and `w'` give the same element. Then `b = a_w^-1 a_w'` is an affine map
    `ξ ↦ γ·ξ + u` fixing `S = φ(C^n)` pointwise.
  - For `s, s_0 ∈ S`, `γ·(s − s_0) = s − s_0`. So `(s − s_0)(γ^-1 m − m) = 0` for all `m`.
  - By affine spanning, the only `m'` with `(s − s_0)(m') = 0` for all `s, s_0` is `m' = 0`. So
    `γ^-1 m = m` for all `m`, and `γ = 1`. Then `u = s − s = 0`.
  - Hence `λ ↦ a_λ` is a well-defined homomorphism `Λ → Aff(M^)`. Write `a_λ(ξ) = q(λ)·ξ + v_λ`.
    Then `q : Λ → GL_2(R)` is a homomorphism, and `Γ := q(Λ) = ⟨γ_i⟩ ⊇ EL_2(R)`.
- **The module.** Define `ι : M → C(C^n, F_p)` by `ι(m)(x) = φ(x)(m)`.
  - It is locally constant, because `φ` is continuous for the pointwise topology and `F_p` is
    discrete.
  - It is additive.
  - From `φ(x) = q(λ)·φ(λ^-1 x) + v_λ` we get `φ(λ^-1 x)(m) = φ(x)(q(λ)m) − v_λ(q(λ)m)`, i.e.
    `λ·ι(m) = ι(q(λ)m) − v_λ(q(λ)m)·1`.
  - Let `Z = F_p·1` and `M' = ι(M) + Z`. Then `M'` is a `Λ`-invariant subgroup of `C(C^n, F_p)`.
  - The map `ῑ : M → M'/Z` is surjective and `Λ`-equivariant for `q`. It is injective because
    `φ` is affinely spanning (`ι(m) ∈ Z` means `x ↦ φ(x)(m)` is constant).
- **The subgroup.** By Step 1, `G := M' ⋊ Λ ≤ nV`.
  - `M'` is infinite, since `M'/Z ≅ M` and `R` is infinite.
  - `Z` has order `p`, is central in `G` (`Λ` fixes constants, `M'` is abelian), and
    `G/Z ≅ M ⋊_q Λ`.

## Step 3 (transfer lemma): relative (T) passes through the quotient `q`

**Lemma T.** Let `M` be a countable abelian group of exponent `p`, and `Γ ≤ Aut(M)` a countable
subgroup. Suppose `(M ⋊ Γ, M)` has relative (T). Let `Λ` be a group with a homomorphism
`q : Λ → Γ` onto `Γ`. Then `(M ⋊_q Λ, M)` has relative (T).

*Proof.*
- **Splitting the Kazhdan set.** Let `(Q, ε)` witness relative (T) for `(M ⋊ Γ, M)`. Write each
  `s ∈ Q` as `s = m_s γ_s`. Put `Q_M = {m_s}` and `Q_Γ = {γ_s}`. Since
  `‖π(mγ)ξ − ξ‖ ≤ ‖π(m)ξ − ξ‖ + ‖π(γ)ξ − ξ‖`, the pair `(Q_M ∪ Q_Γ, ε/2)` also witnesses relative
  (T).
- **Candidate set.** Choose `Q_Λ ⊆ Λ` finite with `q(Q_Λ) = Q_Γ`. Put `δ = min(ε/4, ε^2/8)`. We
  show that `(Q_M ∪ Q_Λ, δ)` witnesses relative (T) for `(M ⋊_q Λ, M)`.
- **Setup.** Let `π` be a unitary representation of `M ⋊_q Λ` on `H`, and `ξ` a unit vector moved
  by less than `δ` by every element of `Q_M ∪ Q_Λ`. Assume, for contradiction, that `H` has no
  nonzero `M`-invariant vector.
- **Spectral measure.** Let `E` be the projection-valued measure on the compact group `M^` with
  `π(m) = ∫ e(χ(m)) dE(χ)`.
  - `E({0})` is the projection onto `H^M`, so `E({0}) = 0`.
  - `π(λ)π(m)π(λ)^-1 = π(q(λ)m) = ∫ e((q(λ)^-1·χ)(m)) dE(χ)`. By uniqueness of spectral measures,
    `π(λ)E(B)π(λ)^-1 = E(q(λ)·B)`.
  - Let `ν = ⟨E(·)ξ, ξ⟩`, a Borel probability with `ν({0}) = 0`. Then
    `⟨E(B)π(λ)ξ, π(λ)ξ⟩ = ν(q(λ)^-1·B)`. So the spectral law of `π(λ)ξ` is `q(λ)_*ν`, which
    depends only on `q(λ)`.
  - For Borel `|f| ≤ 1` and unit vectors `η, ξ`, `|⟨f(E)η,η⟩ − ⟨f(E)ξ,ξ⟩| ≤ 2‖η − ξ‖`. So
    `‖q(λ)_*ν − ν‖_TV ≤ 2‖π(λ)ξ − ξ‖`.
- **Koopman model on the quotient.**
  - Choose weights `c_γ > 0` over the countable `Γ` with `Σ_γ c_γ = 1`, and put
    `ν~ = Σ_γ c_γ γ_*ν`. It is quasi-invariant under `Γ`, and `γ_*ν ≪ ν~` for every `γ ∈ Γ`.
  - Let `ρ` be the unitary representation of `M ⋊ Γ` on `L^2(M^, ν~)` given by
    `(ρ(m)f)(χ) = e(χ(m)) f(χ)` and
    `(ρ(γ)f)(χ) = (d γ_*ν~/dν~)(χ)^(1/2) f(γ^-1·χ)`.
  - The covariance `ρ(γ)ρ(m)ρ(γ)^-1 = ρ(γm)` holds because `e((γ^-1·χ)(m)) = e(χ(γm))`.
- **The vector.** Let `η = (dν/dν~)^(1/2)`, a unit vector.
  - `ρ(γ)η = (d γ_*ν/dν~)^(1/2)`.
  - For `m ∈ Q_M`: `‖ρ(m)η − η‖^2 = ∫ |e(χ(m)) − 1|^2 dν = ‖π(m)ξ − ξ‖^2 < δ^2`.
  - For `γ = q(λ)` with `λ ∈ Q_Λ`, let `a` and `b` be the densities of `γ_*ν` and `ν`. Since
    `(√a − √b)^2 ≤ |√a − √b|(√a + √b) = |a − b|`,
    `‖ρ(γ)η − η‖^2 = ∫ (√a − √b)^2 dν~ ≤ ∫ |a − b| dν~ = ‖γ_*ν − ν‖_TV ≤ 2‖π(λ)ξ − ξ‖ < 2δ`.
  - So `η` is moved by less than `δ < ε/2` by each element of `Q_M`, and by less than
    `(2δ)^(1/2) ≤ ε/2` by each element of `Q_Γ`.
- **Contradiction.** By relative (T) for `(M ⋊ Γ, M)` there is a nonzero `M`-invariant
  `f ∈ L^2(ν~)`.
  - For each of the countably many `m`, `e(χ(m)) = 1` for `ν~`-almost every `χ` with `f(χ) ≠ 0`.
  - So `f` is supported, up to a null set, on `{χ : χ(m) = 0 for all m} = {0}`.
  - But `ν~({0}) = Σ c_γ ν(γ^-1·{0}) = Σ c_γ ν({0}) = 0`. So `f = 0`, a contradiction. ∎

**Application.**
- `(M ⋊ EL_2(R), M)` has relative (T) by `elementary-linear-semidir-pair-relative-t`.
- It passes to `(M ⋊ Γ, M)` for `Γ = q(Λ) ⊇ EL_2(R)`, with the same `(Q, ε)`, by restricting
  representations.
- `Γ ≤ GL_2(R)` is countable, since `R` is.
- By Lemma T, `(M ⋊_q Λ, M)` has relative (T). By Step 2 this pair is `(G/Z, M'/Z)`.

## Step 4 (finite central kernel): `(G, M')` has relative (T)

- Let `(Q_1, δ_1)` witness relative (T) for `(G/Z, M'/Z)`, with `δ_1 < 1`. Lift `Q_1` to a finite
  `Q~_1 ⊆ G`. Put `Q = Q~_1 ∪ Z` and `δ' = δ_1/3`.
- Let `π` be a unitary representation of `G` with a unit `ξ` moved by less than `δ'` by each
  element of `Q`.
- `P = (1/p) Σ_(z ∈ Z) π(z)` is the orthogonal projection onto `H^Z`. It commutes with `π(G)`,
  because `Z` is central.
- `‖ξ − Pξ‖ ≤ (1/p) Σ_z ‖ξ − π(z)ξ‖ < δ'`. So `‖Pξ‖ > 1 − δ' ≥ 2/3`.
- For `s ∈ Q~_1`, `‖π(s)Pξ − Pξ‖ = ‖P(π(s)ξ − ξ)‖ < δ'`. So the unit vector `Pξ/‖Pξ‖` is moved by
  less than `δ'/(2/3) = δ_1/2 < δ_1`.
- `H^Z` is a representation of `G/Z`. By the choice of `(Q_1, δ_1)` it has a nonzero
  `M'/Z`-invariant vector, which is an `M'`-invariant vector of `π`.

## Step 5 (Schoenberg): relative (T) for an infinite subgroup kills the Haagerup property

Suppose `nV` had a proper conditionally negative definite function `ψ`. Restricting it gives one
on `G`, since `G ≤ nV` by Step 1. Normalize so that `ψ(1) = 0` and `ψ(g^-1) = ψ(g)`.

- **Schoenberg.** Each `φ_t = e^(−tψ)`, `t > 0`, is positive definite. *Proof.*
  - The kernel `K(x,y) = ψ(x) + ψ(y) − ψ(y^-1 x)` is positive definite. Given `c_1..c_N` at
    `x_1..x_N`, append `x_0 = 1` with `c_0 = −Σ c_i`. Conditional negativity of
    `(x,y) ↦ ψ(y^-1 x)` on these `N+1` points gives `Σ_(i,j) c_i c̄_j K(x_i, x_j) ≥ 0`.
  - `exp(tK) = Σ t^j K^j/j!` is positive definite by the Schur product theorem.
  - `φ_t(y^-1 x) = e^(−tψ(x)) exp(tK(x,y)) e^(−tψ(y))` is then positive definite.
  - This is BdlHV, Theorem C.3.2.
- **GNS.** Let `(π_t, H_t, ξ_t)` be the GNS triple of `φ_t`, so `⟨π_t(g)ξ_t, ξ_t⟩ = φ_t(g)`.
  - `φ_t` is `C_0`, because `ψ` is proper.
  - So every coefficient `⟨π_t(g)u, v⟩` is `C_0`. This holds for `u, v` in the span of `π_t(G)ξ_t`
    (finite sums of translates of `φ_t`), and passes to all `u, v` by uniform limits.
- **Almost invariance.** `‖π_t(s)ξ_t − ξ_t‖^2 = 2 − 2e^(−tψ(s))` tends to `0` as `t → 0`, for each
  `s` in the finite set `Q` of Step 4.
- **Contradiction.** For small `t`, Step 4 gives a nonzero `M'`-invariant `u ∈ H_t`. Then
  `g ↦ ⟨π_t(g)u, u⟩` equals `‖u‖^2 ≠ 0` on the infinite set `M'`, which contradicts `C_0`. ∎

This proves Theorem R.

## Step 6 (generators of `EL_2(F_p[t,t^-1])`)

- **Conjugation by `h`.** `h e_12(r) h^-1 = e_12(t^2 r)` and `h e_21(r) h^-1 = e_21(t^-2 r)`.
- **Upper shears.** `e_12` is additive, and `e_12(c) = e_12(1)^c` for `c ∈ F_p`. Every Laurent
  polynomial is an `F_p`-combination of `t^(2j)` and `t^(2j+1)`, and
  `e_12(t^(2j)) = h^j e_12(1) h^-j` and `e_12(t^(2j+1)) = h^j e_12(t) h^-j`. So
  `⟨e_12(1), e_12(t), h⟩ ⊇ e_12(R)`.
- **Lower shears.** Symmetrically, `e_21(t^(2j)) = h^-j e_21(1) h^j` and
  `e_21(t^(2j+1)) = h^-j e_21(t) h^j`.
- **The torus is elementary.** Let `w(u) = e_12(u) e_21(−u^-1) e_12(u)` for a unit `u`. Then
  `h = w(t) w(1)^-1`, so `h ∈ EL_2(R)`.
- Hence the five elements generate exactly `EL_2(R)`.
- Checked by exact computation in `experiments/nv-break-2026-09-17/check_char_p_burger_lamp.py`
  (`check_identities`, for `p = 2, 3, 5`).

## Step 7 (Proposition B): the torus generator lifts in 2V

- **The baker map is in 2V.** `B(0u, y) = (u, 0y)` and `B(1u, y) = (u, 1y)`. On the two boxes
  `[a] × C` it replaces the prefix pair `(a, ∅)` with `(∅, a)`.
- **Shift coordinates.** Let `Θ : C^2 → {0,1}^Z` be `Θ(x, y)_j = x_j` for `j ≥ 0` and
  `Θ(x, y)_(−j−1) = y_j` for `j ≥ 0`. It is a homeomorphism.
  - `B(x, y) = (x_1 x_2 ..., x_0 y_0 y_1 ...)`. So `Θ(B(x,y))_j = x_(j+1)` for `j ≥ 0`,
    `Θ(B(x,y))_(−1) = x_0`, and `Θ(B(x,y))_(−j−1) = y_(j−1)` for `j ≥ 1`.
  - That is, `Θ B Θ^-1 = S`, the left shift `(Sz)_i = z_(i+1)`.
- **Block code.** Let `2^k ≥ p^2`, `τ : {0,1}^k → F_p^2` a surjection, and
  `φ_0 : {0,1}^Z → (F_p^2)^Z` with `φ_0(z)_j = τ(z_(jk), ..., z_(jk+k−1))`.
  - `φ_0` is continuous and surjective.
  - `φ_0 ∘ S^k = (σ × σ) ∘ φ_0`, where `σ × σ` shifts both coordinates.
- **Reversal.** Let `ψ(α, β) = (α∘(−id), β)`, i.e. `(ψα)_j = α_(−j)`. Then
  `ψ ∘ (σ × σ) = (σ^-1 × σ) ∘ ψ`, because `(σα)_(−j) = α_(−j+1) = (σ^-1 ψα)_j`.
- **Conclusion.** `φ = ψ ∘ φ_0 ∘ Θ : C^2 → M^` is continuous and surjective, and
  `φ∘B^k = (σ^-1 × σ)∘φ = h·φ`. It is affinely spanning because it is surjective.
- **The case `p = 2`, `k = 2`.** Here `τ` is a bijection, so `φ` is a homeomorphism.
- **Check.** `check_baker` in the experiment verifies `Θ B Θ^-1 = S` and `φ∘B^k = h·φ` on windows,
  for `(p, k) = (3, 4)` and `(2, 2)`, with 100 random points each. Output:
  `experiments/nv-break-2026-09-17/check_char_p_burger_lamp.out.txt`.

## Scope

- Theorem R is a sufficient criterion. It proves nothing about `2V` until the shear lifts exist for
  the same `φ`.
- `n = 1` is excluded a posteriori: `V` is Haagerup (Farley), so Theorem R shows that no
  realization exists in `V`.
- Only finitely many lifts are used. The group `Λ` is finitely generated, and `φ` only has to be
  affinely spanning, not injective or surjective.
- `injective-char-p-lamp-realizations-miss-fixed-points` constrains injective `φ` only.
  Non-injective `φ` are untouched by it.
