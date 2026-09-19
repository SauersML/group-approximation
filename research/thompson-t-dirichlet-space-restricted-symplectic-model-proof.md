---
rg: 2
id: thompson-t-dirichlet-space-restricted-symplectic-model-proof
kind: route
title: "PSL_2(Z) maps agreeing at a rational point have the same derivative there, so PPSL_2(Z) is C^1 with Lipschitz log-derivative; Shen's theorem gives Weil-Petersson class and Hu-Shen gives the Hilbert-Schmidt condition; the Euler area computation is the calibration of the PL case"
target: thompson-t-dirichlet-space-restricted-symplectic-model
requires:
  - thompson-t-is-isomorphic-to-ppsl2z
---

Notation as in the target.

## Imports

- (J1) `thompson-t-is-isomorphic-to-ppsl2z` (graph, ESTABLISHED; Haagerup–Olesen Definition 2.1
  and Theorem 2.2, Imbert, Fossas).
- (J2) Y. Shen, *Weil–Petersson Teichmüller space*, Amer. J. Math. 140 (2018), 1041–1074,
  arXiv:1304.3197. Abstract, verbatim as fetched from arXiv on 2026-09-19: "A sense-preserving
  homeomorphism h on the unit circle belongs to the Weil-Petersson class ... if and only if h is
  absolutely continuous such that log h' belongs to the Sobolev class H^(1/2)." (The elided words
  restate the definition of the class through quasiconformal extensions with square-integrable
  Beltrami coefficients.)
- (J3) Y. Hu, Y. Shen, *On quasisymmetric homeomorphisms*, Israel J. Math. 191 (2012), 209–226.
  Quoted as Corollary 1.5 of arXiv:2609.08539 (*Real-analytic realization of universal
  Teichmüller space via complex-structures on H^{1/2}*), verbatim as fetched on 2026-09-19:
  "The results of [8] show that the anti-analytic pull-back is compact exactly on the symmetric
  class and Hilbert–Schmidt exactly on the Weil–Petersson class." and "Corollary 1.5. Let
  h∈QS(S¹). Then h is symmetric ⟺ J_h−H is compact, and h∈WP(S¹) ⟺ J_h−H is Hilbert–Schmidt."
  There `[8]` is Hu–Shen, `H` is the Hilbert transform on `H^{1/2}(S^1)` and `J_h = V_h H V_h^{-1}`
  with `V_h φ = φ ∘ h` the pull-back.
  - *Caveat.* (J3) was read through a secondary source, not from Hu–Shen directly. The
    normalization of `H^{1/2}` (mod constants) is the standard one of that literature.
- (J4) Standard: a quasisymmetric `h` makes `V_h` bounded and invertible on `H^{1/2}(S^1)/R`
  (Nag–Sullivan). For the bi-Lipschitz maps used here it is elementary from the Douglas formula
  `‖φ‖² ≍ ∬ |φ(x) − φ(y)|² / sin²(π(x − y)) dx dy`. A `C^1` diffeomorphism is bi-Lipschitz and
  quasisymmetric.

## Step 1. PPSL_2(Z) is C^1 (part 1)

*Matching derivatives.* Let `A = [[α, β], [γ', δ]] ∈ SL_2(Z)` and `p/q` a reduced fraction with
`A(p/q) ≠ ∞`. Then `A'(x) = (γ'x + δ)^{-2}` and `γ'(p/q) + δ = (γ'p + δq)/q`. The vector
`(αp + βq, γ'p + δq) = A(p, q)` is primitive, so `q' = |γ'p + δq|` is the reduced denominator of
`A(p/q)`. Hence `A'(p/q) = q²/q'²` depends only on `p/q` and `A(p/q)`. If `p/q = ∞` or
`A(p/q) = ∞`, pre- or post-compose with `S(x) = −1/x ∈ PSL_2(Z)`. This uses the analytic chart
`x ↦ −1/x` at `∞` and reduces to the finite case. So two elements of `PSL_2(Z)` that agree at a
rational point have the same derivative there.

*Consequence.* Let `g ∈ PPSL_2(Z)`. By (J1) it has finitely many breakpoints, all rational, and
agrees with some `A_i ∈ PSL_2(Z)` on each closed complementary arc `I_i`. At a common endpoint
the two adjacent pieces agree in value (`g` is continuous), hence in derivative. So `g` is a `C^1`
diffeomorphism of `RP^1`, real-analytic on each closed arc `I_i` up to its endpoints.

Conjugating by the analytic diffeomorphism `ψ₀` preserves all of this. So `h = ψ₀gψ₀^{-1}` is
`C^1` on `R/Z`, `h' > 0` is continuous, and `h'` is analytic on each of finitely many closed arcs.
Therefore `h'` and `log h'` are Lipschitz. Lipschitz functions lie in `H^{1/2}`, since
`∬|f(x) − f(y)|²/sin²(π(x − y)) ≤ L²∬ (x − y)²/sin²(π(x − y)) < ∞`. `h` is absolutely continuous.
By (J2), `h` is of Weil–Petersson class. ∎

## Step 2. The restricted symplectic condition (part 2)

- `ρ(g) = V_{g^{-1}}` is bounded and invertible on `H` by (J4). It preserves mean-zero classes
  modulo constants, and `ρ(gh) = ρ(g)ρ(h)`.
- *Symplectic.* For `C^1` periodic `φ, ψ` and a `C^1` lift `f̃`,
  `ω(φ∘f̃, ψ∘f̃) = ∫_0^1 φ(f̃x) ψ'(f̃x) f̃'(x) dx = ∫_{f̃(0)}^{f̃(0)+1} φ ψ' = ω(φ, ψ)`, using
  periodicity. Both sides are continuous on `H × H`, since `|ω(φ, ψ)| ≤ ‖φ‖ ‖ψ‖` by
  Cauchy–Schwarz in the Fourier formula. `C^1` functions are dense and `V_f` is bounded, so
  `ρ(g)` is symplectic on `H`.
- *Hilbert–Schmidt.* `g^{-1}` is again an element of the smoothed model, so it is WP by Step 1. By (J3), `J_{g^{-1}} − H` is Hilbert–Schmidt. Then
  `[ρ(g), J] = V_{g^{-1}}H − HV_{g^{-1}} = (J_{g^{-1}} − H)V_{g^{-1}}` is Hilbert–Schmidt. ∎

## Step 3. The cocycle and its area (part 3)

This repeats the calibration of `integrably-paired-cup-products-exact-proof`, Step 3, for `C^1`
lifts instead of PL ones. It uses only monotonicity, `f̃(x + 1) = f̃(x) + 1`, and substitution.

- `u_f` is `C^1` and 1-periodic, so its class lies in `H`. Changing the lift adds a constant.
- `u_{fg} = u_f ∘ g̃ + u_g`. Apply it to `u_{(gh)^{-1}} = u_{h^{-1}g^{-1}}`:
  `u_{h^{-1}} ∘ g̃^{-1} + u_{g^{-1}} = ρ(g)c(h) + c(g)`. So `c(gh) = c(g) + ρ(g)c(h)`.
- *Area.* `u_{g^{-1}} ∘ g̃ = id − g̃ = −u_g`, and similarly `u_{h^{-1}} = −u_h ∘ h̃^{-1}`. By
  symplectic invariance under `g̃` and then `h̃`,
  `Ω(g, h) = ω(u_{g^{-1}}, u_{h^{-1}}∘g̃^{-1}) = ω(−u_g, u_{h^{-1}}) = ω(u_g, u_h∘h̃^{-1})
  = ω(u_g∘h̃, u_h)`.
- Then `ω(u_g∘h̃, u_h) = ∫_0^1 u_g(h̃x) d(h̃x) − ∫_0^1 u_g(h̃x) dx = ∫_0^1 u_g − ∫_0^1 u_g∘h̃
  = −D(g, h)`.
- *Euler cocycle.* `A(f̃) = ∫_0^1 u_f` satisfies `A(z^k f̃) = A(f̃) + k` and
  `A(f̃g̃) = A(g̃) + ∫_0^1 u_f∘g̃ = A(f̃) + A(g̃) + D(f, g)`. Apply `A` to
  `σ(g)σ(h) = z^{ε(g,h)}σ(gh)`: `ε(g,h) + β_A(gh) = β_A(g) + β_A(h) + D(g,h)`, so
  `D = ε − dβ_A` and `Ω = −ε + dβ_A`.

*Identification with T̄.* `T̄` is the lift group of the PL model. The smoothed model is
conjugate to it by `k = ψ₀ ∘ φ^{-1}` (J1), and a lift `k̃` conjugates the two lift groups, sending
`z` to `z^{±1}`. So the extensions agree up to the sign of `z`. A splitting `β` with
`β(z, ·) = 1` for one gives `±β` for the other. ∎
