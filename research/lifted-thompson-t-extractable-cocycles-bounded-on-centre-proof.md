---
rg: 2
id: lifted-thompson-t-extractable-cocycles-bounded-on-centre-proof
kind: route
title: "Paradoxical triple of T on the circle gives a spectral gap; the commuting-cocycle identity for the central z turns it into a bound on the centre"
target: lifted-thompson-t-extractable-cocycles-bounded-on-centre
requires:
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

Notation as in the target. Imports: (S1) an amenable group acting on a compact metrizable space
fixes a Borel probability measure; (S2) if `σ` is weakly contained in `ρ`, then
`sp(σ(x)) ⊆ sp(ρ(x))` for every self-adjoint `x ∈ C[T̄]` (the identity on `C[T̄]` extends to a
surjection `C*_ρ → C*_σ`; Bekka-de la Harpe-Valette, *Kazhdan's property (T)*, Appendix F, not
re-read at source); (S3) item 2 of `lifted-thompson-t-perfect-centre-cubically-elliptic`
(`T̄` is perfect).

## Step 1. The paradoxical inequality on S^1

Let `μ` be a finite positive Borel measure on `S^1` and `δ ≥ 0` with
`|μ(h_i B) − μ(B)| ≤ δ` for all Borel `B` and `i = 1, 2, 3`. Then `μ(S^1) ≤ 5δ`.

Proof. Put `I = [0,1/2)`, `J = [1/2,1)` and `a = μ(I)`. From the table,
`h_1 I = [0,1/4)`, `h_2 I = [1/4,1/2)` and `h_3 I = J`.
- `a = μ[0,1/4) + μ[1/4,1/2) = μ(h_1 I) + μ(h_2 I) ≥ 2a − 2δ`, so `a ≤ 2δ`.
- `μ(J) = μ(h_3 I) ≤ a + δ ≤ 3δ`.
- So `μ(S^1) = a + μ(J) ≤ 5δ`. ∎

## Step 2. Item 1 (gap)

Let `E` be a circle extraction, `ξ ∈ H`, `ε = max_i ‖ρ(ĥ_i)ξ − ξ‖` and `μ = E(ξ)`. By
equivariance `E(ρ(ĥ_i)ξ) = h_{i*}μ`, and `‖ρ(ĥ_i)ξ‖ = ‖ξ‖`. So the Lipschitz condition gives, for
every Borel `B'`, `|μ(h_i^{-1}B') − μ(B')| ≤ 2ε‖ξ‖`. Put `B' = h_i B`:
`|μ(B) − μ(h_i B)| ≤ 2ε‖ξ‖` for every `B`. Step 1 with `δ = 2ε‖ξ‖` gives
`‖ξ‖² = μ(S^1) ≤ 10 ε ‖ξ‖`, so `‖ξ‖ ≤ 10ε`. Then
`Σ_i ‖ρ(ĥ_i)ξ − ξ‖² ≥ ε² ≥ ‖ξ‖²/100`, that is `c(ρ) ≥ 1/100`. ∎

## Step 3. Item 2 (centre bound)

Let `b` be a 1-cocycle, `b(gh) = b(g) + ρ(g)b(h)`. For `h ∈ T̄` and `M ∈ Z`, `z^M h = h z^M`, so
`b(z^M) + ρ(z^M) b(h) = b(h) + ρ(h) b(z^M)`, that is

`(ρ(h) − 1) b(z^M) = (ρ(z^M) − 1) b(h)`.

The right side has norm at most `2‖b(h)‖`. Take `ξ = b(z^M)` and `h = ĥ_i`, and sum:
`c(ρ) ψ(z^M) ≤ Σ_i ‖(ρ(ĥ_i) − 1) b(z^M)‖² ≤ 4 Σ_i ψ(ĥ_i)`. With `c(ρ) ≥ 1/100` this is
`ψ(z^M) ≤ 400 Σ_i ψ(ĥ_i)`, uniformly in `M`. ∎

## Step 4. Item 3 (closure)

Put `Δ_ρ = Σ_i (2 − ρ(ĥ_i) − ρ(ĥ_i)^*)`, the image of a self-adjoint element of `C[T̄]`. Then
`⟨Δ_ρ ξ, ξ⟩ = Σ_i ‖ρ(ĥ_i)ξ − ξ‖²`, so `c(ρ) = min sp(Δ_ρ)`.
- *Direct sums and subrepresentations.* `Δ` is diagonal for an orthogonal decomposition into
  subrepresentations, and the minimum of the spectrum of a direct sum is the infimum over the
  summands; for a subrepresentation it can only increase.
- *Weak containment.* By (S2), `sp(Δ_σ) ⊆ sp(Δ_ρ)`, so `c(σ) ≥ c(ρ)`.
- *Contribution of good parts.* If `ρ = ⊕ρ_α` and `b = ⊕b_α` (each `b_α` is a cocycle into
  `ρ_α`), sum Step 3 over the `α` with `c(ρ_α) ≥ 1/100`:
  `Σ_α ψ_α(z^M) ≤ 400 Σ_i Σ_α ψ_α(ĥ_i) ≤ 400 Σ_i ψ(ĥ_i)`. ∎

## Step 5. Item 4 (centre-fixed part)

`H^z` is invariant under `ρ(T̄)`, since `z` is central. Let `ρ_0` and `b_0` be the restrictions
and projections to it; `b_0` is a cocycle into `ρ_0`.
- The identity of Step 3 in `ρ_0`, where `ρ_0(z) = 1`, gives `(ρ_0(h) − 1) b_0(z) = 0` for all
  `h`. So `b_0(z)` is a `T̄`-invariant vector.
- Let `Q` be the projection of `H^z` onto the `T̄`-invariant vectors. Since `Qρ_0(g) = Q`, the map
  `g ↦ Q b_0(g)` is a homomorphism `T̄ → (QH^z, +)`, which is `0` by (S3).
- So `b_0(z) = Q b_0(z) = 0`, and `b_0(z^M) = Σ_{j<M} ρ_0(z^j) b_0(z) = 0` for `M ≥ 0`; for
  `M < 0`, `b_0(z^M) = −ρ_0(z^M) b_0(z^{−M}) = 0`. ∎

## Step 6. The examples

- *(a)* `E(ξ)(B) = ⟨P(B)ξ, ξ⟩` has mass `‖ξ‖²`. Equivariance:
  `⟨P(B)ρ(g)ξ, ρ(g)ξ⟩ = ⟨P(ḡ^{-1}B)ξ, ξ⟩ = (ḡ_*E(ξ))(B)`. Lipschitz:
  `E(ξ)(B) − E(η)(B) = ⟨P(B)(ξ − η), ξ⟩ + ⟨P(B)η, ξ − η⟩`, of modulus at most
  `‖ξ − η‖(‖ξ‖ + ‖η‖)`.
- *(b)* Multiplication by `1_{π^{-1}B}`, for the equivariant map `π : Y → S^1`, commutes with the
  cocycle twist and is a PVM with `ρ(g) P(B) ρ(g)^{-1} = P(ḡB)`. So (b) is a case of (a).
- *(c)* `ρ_θ(g)` is unitary on `H_θ`: `|f|²` is `1`-periodic and `g` commutes with `z`, so
  `∫_0^1 |f(g^{-1}x)|² (g^{-1})'(x) dx = ∫_{g^{-1}[0,1)} |f|² = ∫_0^1 |f|²`. Also
  `(ρ_θ(z)f)(x) = f(x − 1) = e^{−2πiθ} f(x)`. Multiplication by the periodic function
  `1_{B+Z}` preserves `H_θ` and is covariant as in (b). Steps 1-2 involve no `θ`, so the bound
  is uniform.
- *(d)* `x_*ν` is well defined because the image of `L` fixes `ν`, and
  `E(ρ(g)ξ) = Σ |c_x|² (gx)_*ν = ḡ_*E(ξ)`. The mass is `Σ|c_x|² = ‖ξ‖²`, and
  `|E(ξ)(B) − E(η)(B)| ≤ Σ_x ||c_x|² − |d_x|²| ≤ ‖ξ − η‖(‖ξ‖ + ‖η‖)` by Cauchy-Schwarz. For
  amenable `L` the image is amenable and fixes some `ν` by (S1).

## Step 7. Corollary and remark

- *Corollary.* By Step 5, `ψ(z^M) = ψ_1(z^M)`, where `ψ_1 = ‖b_1‖²` and `b_1` is the component
  in `ρ_1`. If `c(ρ_1) > 0`, Step 3 bounds `ψ_1` on `⟨z⟩`, a contradiction; so `c(ρ_1) = 0`. If
  `ρ_1 ≺ ρ'` with `ρ'` extractable, then `c(ρ_1) ≥ c(ρ') ≥ 1/100` by Steps 2 and 4, again a
  contradiction. `ρ_1` lives on `(H^z)^⊥`, which contains no nonzero `z`-fixed vector.
- *Groupoid remark.* For composable `(g', ḡx)` and `(g, x)`, `σ(g, x)` takes the representative
  `x̃ ∈ [0,1)` into `[0,1)`, and `σ(g', ḡx)` takes that point back into `[0,1)`. So the product is
  the lift of `g'g` that takes `x̃` into `[0,1)`, namely `σ(g'g, x)`. Hence
  `(g, x) ↦ ((ḡ, x), k)` with `g = σ(ḡ, x) z^k` is a groupoid isomorphism onto
  `(T ⋉ S^1) × Z`. A representation of this groupoid on a measurable field over `(S^1, μ)`
  integrates to a representation of `T̄` on `L²` sections, where multiplication by `L^∞(S^1, μ)`
  gives a covariant PVM, which is type (a). ∎
