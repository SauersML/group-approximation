---
rg: 2
id: novikov-level-descent-fails-for-d-shaped-laplacian-systems-proof
kind: route
title: "Explicit depth-1 Novikov certificates in Z[Z^2 x| Z] for both signs, a cube-root-of-unity quotient at level 0, and reduction mod a theta-stable ideal for the gate"
target: novikov-level-descent-fails-for-d-shaped-laplacian-systems
requires:
  - artin-sigma1-is-union-of-finite-depth-level-systems
artifacts:
  - experiments/artin-level-descent-2026-09-17/swap_toy_certificate.py
  - experiments/artin-level-descent-2026-09-17/swap_toy_certificate.log
---

Notation is as in the target. In `G = Z^2 ⋊ Z` every element is uniquely `h t^n` with
`h ∈ H = ⟨a, b⟩` and `n = χ`. `N_χ` consists of the sums `Σ_{n ≥ n_0} c_n t^n` with
`c_n ∈ Z[H]`. Multiplication is `(c t^n)(c' t^m) = c θ^n(c') t^{n+m}`, and `θ` swaps `a, b`.

**Step 1 (level 0 is not onto, part 1(b)).**
- `J_0 = (1 + a, 1 + b + b^2)` in the commutative ring `Z[a^{±1}, b^{±1}]`. The quotient is
  `Z[b^{±1}]/(1 + b + b^2) = Z[ω] ≠ 0`.
- Concretely, `a -> -1, b -> 2` is a ring map to `F_7` that kills both generators
  (`1 + 2 + 4 = 7`).
- `θ(J_0) = (1 + b, 1 + a + a^2)` is its image under the swap, so it is proper too
  (`b -> -1, a -> 2` over `F_7`).

**Step 2 (depth-1 certificate at χ, part 1(a)).**
- Take `λ_ρ = μ_ρ + ν_ρ t^{-1}`, with `ν_1 = c(1 + a + a^2)`, `ν_2 = -c(1 + b)` and
  `c = -b^2`.
- *Level -1:* `Σ ν_ρ θ(σ_ρ) = c(1 + a + a^2)(1 + b) - c(1 + b)(1 + a + a^2) = 0`.
- *Level 0:* the `ν`-contribution is `ν_1 θ(σ_1 ab) + ν_2 θ(σ_2) =
  c(1 + a + a^2)(1 + b)(ab - 1)`.
  - Modulo `J_0`, put `a = -1`, `b = ω`. This gives
    `-ω^2 · 1 · (-ω^2) · (-ω - 1) = ω^4 · ω^2 = 1`, using `-ω - 1 = ω^2`.
  - So `E := 1 - c(1 + a + a^2)(1 + b)(ab - 1)` lies in `J_0`. The script writes
    `-E = μ_1 σ_1 + μ_2 σ_2`, dividing first by the monic `1 + b + b^2` and then by `1 + a`.
    It records `μ_1, μ_2` explicitly.
- Then `Σ_ρ λ_ρ g_ρ = 1 + M`, where `M = Σ μ_ρ σ_ρ p_ρ` is supported at level `1`. The
  script checks the whole product in `ZG`.
- `1 + M` is a unit of `N_χ` (geometric series). So `Σ (1 + M)^{-1} λ_ρ g_ρ = 1`, and the
  system is Novikov onto at `χ`.

**Step 3 (depth-1 certificate at -χ, part 1(a)).**
- Use the generators `t^{-1} g_ρ`, whose `-χ`-level-0 parts are `(1 + b)ab` and
  `1 + a + a^2`.
- Take `λ'_ρ = μ'_ρ + ν'_ρ t`, with `ν'_1 = c'(1 + b + b^2)`, `ν'_2 = -c'(1 + a)ab` and
  `c' = -a^2`. This is the swap image of Step 2.
- The script checks that the `-χ`-level-(-1) part vanishes. It solves for `μ'`, with
  `μ'_1 = (ab)^{-1} q_1`, and checks that `Σ λ'_ρ t^{-1} g_ρ = 1 + M'`, with `M'` at
  `-χ`-level `1`, which is a unit of `N_{-χ}`.
- Since `t^{-1}` is a unit, the left ideal `Σ N_{-χ} g_ρ` is `N_{-χ}`.

**Step 4 (depth exactly 1, and the non-lifting syzygy).**
- `R_0` fails by Step 1, and `R_1` holds by Step 2. In the terms of part 4 of
  `artin-sigma1-is-union-of-finite-depth-level-systems` (whose algebra of Step 5 applies
  verbatim to any D-shaped system with `r = 2`), `θ(ν) = (c'(1 + b + b^2), -c'(1 + a)) ∈
  Syz_0`, and `d^1(θ(ν)) = c'(1 + a)(1 + b + b^2)(ab - 1) ≡ 1 mod θ(J_0)`.
- Suppose `θ(ν)` lifted, as in the lemma of the w17 attempt on the open claim. Then
  subtracting `t^{-1}` times the lift from the exact solution `(1 + M)^{-1} λ` would give a
  solution in `N_{≥0}`. Its level-0 part would put `1 ∈ J_0`, contradicting Step 1.

**Step 5 (obstructions vanish, part 1(c)–(e)).**
- `1 = (1 + b + b^2) - b(1 + b) ∈ J_0 + θ(J_0)`. That sum is the smallest `θ`-stable
  two-sided ideal containing `J_0`, because `θ` is an involution and `Z[H]` is commutative.
  So the `θ`-stable ring hull is everything.
- Any obstruction whose non-vanishing forces Novikov non-surjectivity must vanish, by
  Step 2 and Step 3.
- `σ_1 = Φ_2(a)` and `σ_2 = Φ_3(b)`.
- `p_1 a^2 p_1^{-1} = ab · θ(a^2) · (ab)^{-1} = b^2 ≠ a^2`, and the script checks this. More
  generally `p_1 a^n p_1^{-1} = b^n ≠ a^n` for all `n ≠ 0`, so no power of `x_1 = a` is
  fixed.

**Step 6 (class kill, part 2).** The listed properties are all true of the swap toy. So an
argument using only them would prove formal descent for the toy, which contradicts Steps 1
and 2. In the w17 peeling scheme the failure happens at the syzygy-lifting step, by Step 4.
The obstruction to collapse there is the class `d^1(θ(ν)) = 1` in `Z[H]/θ(J_0)`.

**Step 7 (gate, part 3).**
- *General form.* Suppose `J_0` is two-sided and `θ(J_0) = J_0`. Put `Q = Z[H]/J_0`; `θ`
  descends to `Q`.
  - Reducing coefficients defines a ring homomorphism `N_χ -> Q((t; θ))` to the twisted
    Laurent series, `Σ c_n t^n -> Σ \bar c_n t^n`. It is multiplicative because
    `c θ^n(c')` reduces to `\bar c θ^n(\bar c')` when `J_0` is a `θ`-stable two-sided ideal.
  - Each `g_ρ = σ_ρ(p_ρ - 1)` has its left factor `σ_ρ ∈ J_0`, so `g_ρ` maps to `0`, and so
    does the left ideal `Σ N_χ g_ρ`.
  - If `J_0 ≠ Z[H]`, then `Q ≠ 0` and `1` does not map to `0`. So Novikov onto forces
    `J_0 = Z[H]`.
  - At `-χ` the level-0 ideal is `θ(J_0) = J_0`, and the same argument applies with `t^{-1}`.
- *Abelian case.* If `H` is abelian, then conjugation by `p_ρ = h_ρ t` restricts to `θ` on
  `H`. So the Artin constraint says `θ(x_ρ)^{k_ρ} = x_ρ^{k_ρ}`, and hence
  `(θ(x_ρ) x_ρ^{-1})^{k_ρ} = 1`. With `H` torsion-free this gives `θ(x_ρ) = x_ρ`, so
  `θ(σ_ρ) = σ_ρ`. Then `J_0` is generated by `θ`-fixed elements of a commutative ring, so it
  is `θ`-stable and two-sided, and the general form applies.
- In the toy, the swap moves `x_1 = a`, and the gate does not apply. That is consistent with
  Step 1.
