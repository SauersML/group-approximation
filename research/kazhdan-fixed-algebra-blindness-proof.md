---
rg: 2
id: kazhdan-fixed-algebra-blindness-proof
kind: route
title: Intertwine the Kazhdan projection on the action with the Kazhdan projection on the diagonal ultraproduct
target: kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions
requires:
  - kazhdan-projection-is-norm-limit-of-finite-averages
---

# Proof

Setting as in the claim.

**Step 1, two unitary representations of Γ.** On `L²(X,μ)` let
`κ(γ)ξ = ξ ∘ γ^(-1)` (Koopman). On `L²(D_𝒰, tr)` let `π(γ)η = σ(γ) η σ(γ)^(-1)`.
Conjugation by a permutation maps the diagonal to itself and preserves the
trace, so `π` is a unitary representation.

**Step 2, Θ intertwines them.** In the crossed product `u_γ f u_γ^* = γ·f`, so
`Θ(γ·f) = σ(γ) Θ(f) σ(γ)^(-1)`. `Θ` is trace-preserving, so it extends from
`L^∞(X)` to an isometry `V : L²(X) → L²(D_𝒰)` with `V κ(γ) = π(γ) V`.

**Step 3, the Kazhdan projection.** By
`kazhdan-projection-is-norm-limit-of-finite-averages` there are finitely
supported probability measures `m_k` on `Γ` with `Σ_γ m_k(γ) u_γ → e_Γ` in the
full group C*-algebra. In every unitary representation `ρ`, `ρ(e_Γ)` is the
orthogonal projection onto the `ρ(Γ)`-invariant vectors, and
`ρ(m_k) → ρ(e_Γ)` in operator norm. From Step 2, `V κ(m_k) = π(m_k) V`, hence
`V κ(e_Γ) = π(e_Γ) V`.

**Step 4, the two projections.** `κ(e_Γ)` projects onto `L²(X)^Γ`, which is `C·1`
because `Γ` acts ergodically. `π(e_Γ)` projects onto `L²(D_𝒰)^(σ(Γ))`. This space
equals `L²(D_𝒰^(σ(Γ)))`: an invariant vector splits into real and imaginary
invariant parts, and bounded spectral truncations of a real invariant vector are
invariant elements of `D_𝒰` (trace-preserving automorphisms commute with Borel
functional calculus) converging to it in `L²`. So `π(e_Γ)` restricted to `D_𝒰` is
the conditional expectation onto `D_𝒰^(σ(Γ))`.

**Step 5, conclusion.** For `f ∈ L^∞(X)`,
`E(Θ(f)) = π(e_Γ) V f = V κ(e_Γ) f = V(∫f dμ · 1) = (∫f dμ)·1`.
If `Θ(f) ∈ D_𝒰^(σ(Γ))`, then `Θ(f) = E(Θ(f))` is a scalar, which gives item 1.
Item 2 follows: `L^∞(X)^Γ = C` is `G`-invariant, and `σ(G)` normalizing
`D_𝒰^(σ(Γ))` constrains `σ` on a subspace orthogonal to `Θ(L²_0(X))`.

**Step 6, mixing.** If `G ↷ X` is mixing and `Γ` is infinite, a `Γ`-invariant set
`A` satisfies `μ(γA ∩ A) → μ(A)²` as `γ → ∞` in `Γ`, so `μ(A) = μ(A)²` and `Γ`
acts ergodically. Factors of mixing actions are mixing, and restrictions to
infinite subgroups are mixing, so Steps 1-5 apply to each of them with every
infinite Kazhdan subgroup.

Finite subgroups contribute nothing either. If `Γ` is finite and
`tΓt^(-1) <= Γ`, then `tΓt^(-1) = Γ` by cardinality, so the compression semigroup
is the normalizer and a finite infranormal subgroup is normal. For normal `Γ` the
fixed algebra is automatically `G`-invariant (`g·f` is fixed by `gΓg^(-1) = Γ`).
So every subgroup to which Theorem C applies non-vacuously is infinite, and on a
mixing action it acts ergodically.
