---
rg: 2
id: brin-thompson-nv-max-type-size-functions-are-not-cnd-proof
kind: route
title: "Disjoint-support baker maps make brick size the l^inf norm on Z^3; an integer l^inf^(1/4) certificate, Schoenberg powers and a scaling limit"
target: brin-thompson-nv-max-type-size-functions-are-not-cnd
requires: []
artifacts:
  - experiments/brin-thompson-cnd-2026-09-17/zcube_obstruction.py
  - experiments/brin-thompson-cnd-2026-09-17/zcube_linf_certificates.json
---

Notation is as in the target. `μ` is the product Bernoulli measure on `C^n`, so a brick `[u_1] × ... × [u_n]` has
measure `2^{−Σ|u_i|}`. A brick map `(u_1 s_1, ..., u_n s_n) ↦ (U_1 s_1, ..., U_n s_n)` sends each suffix `s_i` to
coordinate `i` only.

**Step 0 (the elements).** On `[w] × C^{n-1}` the element `b_w^k` acts as follows.
- For `k ≥ 0` it is `(w a s, t, z) ↦ (w s, a t, z)` with `|a| = k`. It is canonical on the `2^k` bricks
  `[w a] × C^{n-1}`.
- For `k < 0` it is `(w s, a t, z) ↦ (w a s, t, z)` with `|a| = |k|`. It is canonical on the `2^{|k|}` bricks
  `[w] × [a] × C^{n-2}`.

It is the identity off `[w] × C^{n-1}`, which is invariant, so `b_w^k ∈ nV`. Disjoint invariant supports give
commutation, so `w ↦ g(w)` is a homomorphism `Z^3 → nV`.

**Step 1 (upper bounds in item 1).**
- Cut `C^n` at `[0]`/`[1]` and `[0]` at `[00]`/`[01]` in the first coordinate.
- On each of the three pieces use the bricks of Step 0. An exponent 0 needs one brick.
- This is a brick diagram with `2^{|m|} + 2^{|p|} + 2^{|q|}` bricks of total length at most `‖w‖_∞ + 2`.

**Step 2 (lower bounds in item 1).** Take any brick diagram of `g(w)`. Consider the piece `P = [1] × C^{n-1}` with
exponent `q`, and let `B = [u_1] × ... × [u_n]` be a diagram brick meeting `P`. Then `W = B ∩ P` is the brick with
first word `u'_1 = the longer of u_1 and "1"`, and `g` acts on `W` by the brick map of `B`.

- **Case `q > 0`.** The second output coordinate of `g` on `P` is `a t`, where `a` is the letters `2..q+1` of the
  first input coordinate.
  - If `|u'_1| < q + 1`, letter `|u'_1| + 1` of the first coordinate is free on `W` and appears in the second output.
  - A brick map's second output depends only on the second input, so this is impossible.
  - Hence `|u'_1| ≥ q + 1`.
- **Case `q < 0`.** The first output is `1 a s`, where `a` is the first `|q|` letters of the second input.
  - If `|u_2| < |q|`, a free letter of the second input appears in the first output, which a brick map cannot do.
  - Hence `|u_2| ≥ |q|`.

In both cases `μ(W) ≤ 2^{−1−|q|}` and the total length of `B` is at least `|q|`. The diagram bricks meeting `P` cover
`P`, which has measure `1/2`, so there are at least `2^{|q|}` of them.

The same argument on `[00] × C^{n-1}` (measure `1/4`, pieces of measure `≤ 2^{−2−|m|}`) and on `[01] × C^{n-1}` gives
`L(g(w)) ≥ 2^{‖w‖_∞}` and `D(g(w)) ≥ ‖w‖_∞`. The script checks item 1 against the exact DP for `|m|, |p|, |q| ≤ 3`
(343 elements, no failure).

**Step 3 (a finite non-negative-type certificate).** Let `S = {−5..5}^3` and `K_β(x, y) = ‖x − y‖_∞^β`.
- `zcube_linf_certificates.json` stores an integer vector `c ∈ Z^S` with `Σ c_x = 0`.
- For `d = 1..10` let `N_d = Σ_{‖x−y‖_∞ = d} c_x c_y`. These are integers.
- `N = (15670247076800, 16199212128578, −23764547649800, −56104820640574, −31873431718404, 25369767932998,
  53704845267188, 31012499925864, −8738814997612, −22474956586490)`.
- So `Q_{1/4} = Σ_d N_d d^{1/4} ≈ 7.6712e11 > 0`. `zcube_obstruction.py --verify` recomputes `N_d` with integers and
  `Q` in 60-digit Decimal arithmetic, so rounding is negligible against `Q`.

Hence `K_{1/4}` is not cnd on `S`. The file also holds certificates for `β = 1` on `{−1..1}^3` and `β = 1/2` on
`{−2..2}^3`.

**Step 4 (all β ≥ 1/4).** Claim: if a symmetric kernel `K ≥ 0` with zero diagonal is cnd on a finite set `S`, then
`K^α` is cnd on `S` for `0 < α < 1`.
1. Fix `x_0 ∈ S` and set `A(x, y) = K(x, x_0) + K(y, x_0) − K(x, y)`.
   - For `v ∈ R^S`, the vector `c = v − (Σ v) δ_{x_0}` sums to zero.
   - Expanding, `Σ c_x c_y K = −Σ v_x v_y A`, so `A` is positive semidefinite.
2. By the Schur product theorem `e^{tA}` is psd for `t ≥ 0`, so `e^{−tK} = D e^{tA} D` with
   `D = diag(e^{−t K(x, x_0)})` is psd.
3. For zero-sum `c`: `Σ c_x c_y (1 − e^{−tK}) = −Σ c_x c_y e^{−tK} ≤ 0`, so `1 − e^{−tK}` is cnd.
4. `K^α = (α/Γ(1−α)) ∫_0^∞ (1 − e^{−tK}) t^{−1−α} dt` entrywise, a positive combination of cnd kernels, so it is cnd.

If `K_β` were cnd on `S` for some `β > 1/4`, then `K_{1/4} = K_β^{1/(4β)}` would be cnd, contradicting Step 3.
So for every `β ≥ 1/4` there is `c^{(β)}` with `Σ c = 0` and `Q_β = Σ c_x c_y ‖x − y‖_∞^β > 0`.

**Step 5 (scaling, item 2).**
1. `G(λ) → ∞`.
   - By hypothesis `G > 0` on some `[λ_0, ∞)`.
   - Choose `0 < ε < 1` with `2^β − ε > 1`, and `λ_1 ≥ λ_0` with `|G(λ r)/G(λ) − r^β| ≤ ε` for `λ ≥ λ_1` and
     `r ∈ [1, 2]`.
   - Then `G(λ) ≥ (1 − ε) G(λ_1) =: c_0 > 0` on `[λ_1, 2λ_1]`, and `G(2λ) ≥ (2^β − ε) G(λ)` for `λ ≥ λ_1`.
   - Writing `λ = 2^k μ` with `μ ∈ [λ_1, 2λ_1)` gives `G(λ) ≥ (2^β − ε)^k c_0 → ∞`.
2. Fix `β`, `c = c^{(β)}` on `S`, `M ∈ R`, and for `λ ∈ N` put `g_x = g(λ x)`. By Step 0, `g_x^{-1} g_y = g(λ(y − x))`.
   The quadratic form of `ψ + M(1 − δ_e)` is
   `Q(λ) = Σ_{x ≠ y} c_x c_y ψ(g(λ(y − x))) + ψ(e) Σ c_x^2 − M Σ c_x^2`, using `Σ_{x≠y} c_x c_y = −Σ c_x^2`.
3. For `x ≠ y` write `d = ‖x − y‖_∞ ∈ {1..10}`. Then
   `ψ(g(λ(y−x)))/G(λ) = [ψ(g(λ(y−x)))/G(λ d)] · [G(λ d)/G(λ)] → κ d^β`.
4. The terms `ψ(e) Σ c^2` and `M Σ c^2` are constant, and `G(λ) → ∞`. So `Q(λ)/G(λ) → κ Q_β > 0`.
   For large `λ`, `Q(λ) > 0`, and `ψ + M(1 − δ_e)` is not cnd.

**Step 6 (corollaries, item 3).**
- `ψ = G(log L)`: by item 1, `log L(g(w)) = ‖w‖_∞ log 2 + θ_w` with `0 ≤ θ_w ≤ log 3`. By uniform convergence,
  `G(‖w‖_∞ log 2 + θ_w)/G(‖w‖_∞) → (log 2)^β`, so `κ = (log 2)^β`. `G(r) = r^β` gives `(log L)^β`.
- `ψ = G(D)`: `D(g(w)) = ‖w‖_∞ + O(1)`, so `κ = 1`.
- `ψ = G(D)(1 + o(1))` also has `κ = 1`.

**Step 7 (item 4).** Let `x_i` and `c` be as in item 4.
- The `ℓ^∞` distances are `d_12 = d_13 = d_14 = d_23 = d_24 = d_35 = d_45 = 1` and `d_15 = d_25 = d_34 = 2`, so
  `Σ c_i c_j d_ij = 4`.
- With `λ = 29` and item 1, every `i ≠ j` has `29 d_ij log 2 ≤ log L(g_i^{-1} g_j) ≤ 29 d_ij log 2 + log 3`.
- Lower-bound the positive-coefficient pairs and upper-bound the negative ones. The form exceeds
  `2204 log 2 − 2088 log 2 − 72 log 3 = 116 log 2 − 72 log 3 > 0`.
- The last inequality is `2^116 > 3^72`, which is exact integer arithmetic.
