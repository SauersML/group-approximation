---
rg: 2
id: xor-cheeger-rank-one-rounding-proof
kind: route
title: Tensor Poincare puts the SDP vectors near one common line up to measure 4 delta/lambda; threshold-round the clamped twisted projection and fill the transition region by a hyperplane; Cauchy-Schwarz charges the violations sqrt(measure * delta)
target: xor-cheeger-sdp-deficit-at-least-sqrt-gap-times-frustration
requires: []
---

Notation is as in the target claim. Assume `λ > 0`. When `λ = 0` the bounds
read `γ <= ∞` and are trivial. Write `e = (u, v)` for an edge drawn from the
edge law and `σ = σ_uv`. The law is symmetric: `(u, v)` and `(v, u)` have the
same distribution, and each endpoint has marginal `π`. Fix unit vectors
`x_u ∈ R^d` with deficit `δ = E_e ‖x_u − σ x_v‖²/4`. Note
`(1 + σ⟨x_u, x_v⟩)/2 = 1 − ‖x_u − σ x_v‖²/4`.

**Two standard facts.**

* **(F1) Poincaré.** For every `f : V → R^D`,
  `Var_π f := E_π ‖f − E_π f‖² <= (1/λ) · (1/2) E_e ‖f_u − f_v‖²`. Apply the
  variational characterization of `λ = λ_2(I − P)` in `L²(π)` coordinatewise.
  `P` is self-adjoint in `L²(π)` because `w` is symmetric, and its Dirichlet
  form is `⟨f, (I − P) f⟩_π = (1/2) E_e (f_u − f_v)²`.
* **(F2) `λ <= 2`.** Every eigenvalue of the stochastic matrix `P` lies in
  `[−1, 1]`, so every eigenvalue of `I − P` lies in `[0, 2]`.

## Step 1 (one common line, up to measure `τ <= 4δ/λ`)

Let `F_u = x_u x_uᵀ`, with the Frobenius norm. Put `c = σ⟨x_u, x_v⟩`, and use
`σ² = 1`. Then

```text
‖F_u − F_v‖²  =  2 − 2c²  =  2(1 − c)(1 + c)  <=  4(1 − c)  =  2 ‖x_u − σ x_v‖².
```

So `E_e ‖F_u − F_v‖² <= 8δ`. By (F1), `Var_π F <= 4δ/λ`.

Let `M = E_π F = E_π x xᵀ`. It is PSD with trace 1. Let its eigenvalues be
`μ_1 >= μ_2 >= ... >= 0`. Then `Var_π F = E_π ‖F‖² − ‖M‖² = 1 − Σ μ_i²`, and
`Σ μ_i² <= μ_1 Σ μ_i = μ_1`. Set `τ := 1 − μ_1`. It follows that

```text
τ  <=  1 − ‖M‖²  =  Var_π F  <=  4δ/λ.
```

## Step 2 (the twisted projection)

Let `w` be a unit top eigenvector of `M`, and put `g_u = ⟨x_u, w⟩ ∈ [−1, 1]`.
Then

```text
E_e (g_u − σ g_v)²  =  E_e ⟨x_u − σ x_v, w⟩²  <=  E_e ‖x_u − σ x_v‖²  =  4δ,
E_π (1 − g²)  =  1 − wᵀ M w  =  τ.
```

Write `Δg = g_u − σ g_v`. Reversal gives `|g_v − σ g_u| = |Δg|`. Fix
`s = 1/2`. By Markov's inequality applied to `1 − g² >= 0`,

```text
p  :=  P_π[ |g| < s ]  <=  P_π[ 1 − g² >= 1 − s² ]  <=  τ/(1 − s²)  =  (4/3) τ  <=  16δ/(3λ).
```

## Step 3 (the rounding `R(x)`)

Let `h(t) = max(−1, min(1, t/s))`, and put `y_u = h(g_u)`. `h` is odd, so
`σ y_v = h(σ g_v)`. Draw `θ ~ U(0,1)` and an independent standard Gaussian
`ζ ∈ R^d`.

* A vertex with `|y_u| > θ` is **determined**, and gets `X_u = sign(y_u)`.
* Every other vertex gets `X_u = sign⟨x_u, ζ⟩`.

Since `θ < 1` almost surely, an undetermined vertex has `|y_u| < 1`, and hence
`|g_u| < s`. The whole rounding runs in polynomial time given `x`, because
`M` and `w` come from one eigendecomposition.

**Threshold part.** Put `a = |y_u|` and `b = |σ y_v| = |y_v|`. Condition on the
event that at least one endpoint is determined and the edge is violated. Then
either exactly one endpoint is determined, which is `θ` in
`[min(a,b), max(a,b))`, or both are determined with `sign(y_u) ≠ sign(σ y_v)`.

* If `y_u` and `σ y_v` have the same sign, only the first case occurs. Its
  probability is `|a − b| = |y_u − σ y_v|`.
* If they have opposite signs, the probability is at most
  `P[θ < max(a,b)] = max(a,b) <= a + b = |y_u − σ y_v|`.
* If one of them is `0`, the first bullet applies with the sign of the other.

So the threshold part contributes at most `|y_u − σ y_v|`.

**Fill part.** A violation with both endpoints undetermined needs
`|g_u| < s`. Given that, it has probability at most
`P_ζ[sign⟨x_u,ζ⟩ ≠ σ sign⟨x_v,ζ⟩] = φ/π`, where `φ = arccos(σ⟨x_u,x_v⟩)`.
Now `‖x_u − σ x_v‖ = 2 sin(φ/2)`, and `sin t >= 2t/π` on `[0, π/2]`. Hence
`φ/π <= sin(φ/2) = ‖x_u − σ x_v‖/2`.

Adding the two parts,

```text
P[R(x) violates e]  <=  |y_u − σ y_v|  +  1{|g_u| < s} · ‖x_u − σ x_v‖/2 .      (★)
```

## Step 4 (a pointwise bound on the clamp)

For real `α, β`,

```text
|h(α) − h(β)|  <=  (1/s) |α − β| · 1{min(|α|,|β|) < s}  +  |α − β|²/(2s²).
```

* If `min(|α|,|β|) < s`, the first term suffices, because `h` is
  `1/s`-Lipschitz.
* If `|α|, |β| >= s` with the same sign, then `h(α) = h(β)`.
* If `|α|, |β| >= s` with opposite signs, then `|α − β| >= 2s`, so the second
  term is `>= 2 >= |h(α) − h(β)|`.

Apply this with `α = g_u` and `β = σ g_v`, so that `|β| = |g_v|`.

## Step 5 (Cauchy–Schwarz)

Take expectations in (★), using Step 4. The events `{|g_u| < s}` and
`{|g_v| < s}` each have probability `p`, by the marginals. So
`P_e[min(|g_u|,|g_v|) < s] <= 2p`. By Cauchy–Schwarz and Step 2,

```text
E_e |Δg| 1{min < s}                <=  sqrt(2p) · sqrt(4δ)  =  2 sqrt(2) sqrt(pδ),
E_e |Δg|²/(2s²)                    <=  4δ/(2s²)             =  8δ,
E_e 1{|g_u| < s} ‖x_u − σx_v‖/2    <=  (1/2) sqrt(p) sqrt(4δ)  =  sqrt(pδ).
```

With `1/s = 2`, `sqrt(pδ) <= sqrt(16/3) · δ/sqrt(λ)`, and `8δ <= 8 sqrt(2) δ/sqrt(λ)`
by (F2), we get

```text
E[violations of R(x)]  <=  (4 sqrt 2 · sqrt(16/3)  +  8 sqrt 2  +  sqrt(16/3)) · δ/sqrt(λ)
                       <=  (13.07 + 11.32 + 2.31) · δ/sqrt(λ)  <=  26.7 δ/sqrt(λ)  <=  27 δ/sqrt(λ).
```

This proves item 1 of the target. Some outcome of the rounding is at least as
good as the mean, so `γ <= 27 δ(x)/sqrt(λ)` for every feasible `x`. The
feasible Gram matrices form a compact set, so an optimal `x` exists, with
`δ(x) = δ_sdp`. This gives `γ <= 27 δ_sdp/sqrt(λ)`, which is item 2. `square`

## Item 3 (the basic SDP at alphabet 2)

At `k = 2`, the constraint `π_uv` is the identity when `σ = +1` and the swap
when `σ = −1`. Both basic SDPs impose `⟨u_1, u_2⟩ = 0` at each vertex:
Figure 1 of AKKSTV, as transcribed in
`unique-games-on-expanding-constraint-graphs-are-easy-citation`, and the
constraint `X_((u,a),(u,b)) = 0` for `a != b` in
`spectral-gap-no-output-kill-proof`. Let `N = ‖u_1‖² + ‖u_2‖²`. This is `1` in
the second normalization and `2` in the first. Figure 1's objective is
`E_i ⟨u_i, v_π(i)⟩ = (1/2) Σ_i`, and the second one is `Σ_i`. So both
objectives equal `(1/N) Σ_i ⟨u_i, v_π(i)⟩`.

Put `s_u = u_1 + u_2` and `z_u = u_1 − u_2`. Orthogonality gives
`‖s_u‖² = ‖z_u‖² = N`. For an edge with sign `σ`,

```text
Σ_i ⟨u_i, v_π(i)⟩  =  (⟨s_u, s_v⟩ + σ ⟨z_u, z_v⟩)/2  <=  (N + σ⟨z_u, z_v⟩)/2 .
```

For `σ = +1` this is `⟨u_1,v_1⟩ + ⟨u_2,v_2⟩`, and for `σ = −1` it is
`⟨u_1,v_2⟩ + ⟨u_2,v_1⟩`. Both follow by expanding. Hence, with unit vectors
`x_u = z_u/sqrt(N)`, the basic objective is at most
`E_e (1 + σ⟨x_u, x_v⟩)/2 <= sdp`. So each basic-SDP deficit is `>= δ_sdp`, and
it is therefore `>= sqrt(λ) γ/27`. The constraint `⟨u_i, v_j⟩ >= 0` of
Figure 1 was not used. `square`

## Tightness computation (odd cycle)

Take the cycle `C_m` with one edge of sign `−1`. Then `γ = 1/m`, and
`λ = 1 − cos(2π/m)`. The vectors `x_j = (cos(jπ/m), sin(jπ/m))` give every
edge angle `π/m`, so `δ_sdp <= (1 − cos(π/m))/2`. This is optimal: the angles
of the edges around the cycle must sum to at least `π`, and `1 − cos` is
convex on `[0, π]`. As `m → ∞`, the ratio `δ_sdp/(sqrt(λ)γ)` tends to
`(π²/4m²)/((sqrt 2 π/m)(1/m)) = π/(4 sqrt 2)`. This part is not needed for
items 1–3.
