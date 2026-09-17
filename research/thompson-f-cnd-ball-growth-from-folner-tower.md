---
rg: 2
id: thompson-f-cnd-ball-growth-from-folner-tower
kind: route
title: Extract a Følner level set from the lazy walk, apply Moore, then feed the second moment bound
target: thompson-f-cnd-certificates-need-near-exponential-ball-growth
requires:
  - thompson-f-folner-function-exceeds-every-tower
  - cnd-ball-growth-bounds-return-probability-for-every-group
---

Notation as in the target. `P f(g) = sum_s mu(s) f(gs)` on `l^2(F)`. `P` is self-adjoint because
`mu` is symmetric, and `P = (I + A)/2` with `||A|| <= 1`, so `0 <= P <= I`. Write `nu` for the spectral
measure of `P` at `delta_e`; it lives on `[0,1]` and `p_k = int x^k d nu`.
The law of the walk at time `m` is `u_m = P^m delta_e`, so `||u_m||^2 = p_{2m}`.

**Step 1. A walk distribution with small Dirichlet energy.**
- *A good time.* `p_0 = 1` and `prod_{m=0}^{N-1} p_{2m+2}/p_{2m} = p_{2N}`, with all `p_{2m} > 0` since
  `mu(e) > 0`. So some `m <= N-1` has `p_{2m+2}/p_{2m} >= p_{2N}^{1/N}`.
- *The energy.* Put `f = u_m >= 0` and `delta = <(I-P) f, f> / ||f||^2`. On `[0,1]` we have `x >= x^2`, so
  `<P f, f> = p_{2m+1} >= p_{2m+2}`.
- *The bound.* Hence `delta <= 1 - p_{2N}^{1/N} <= -log(p_{2N}) / N`, using `1 - e^{-y} <= y`.

**Step 2. Dirichlet form.**
- *Formula.* Right translation preserves counting measure and `mu` is symmetric, so
  `<(I-P) f, f> = 1/2 sum_g sum_s mu(s) (f(g) - f(gs))^2`.
- *For this `mu`.* The term `s = e` vanishes, so `= (1/(4|Γ|)) sum_g sum_{γ in Γ} (f(g) - f(gγ))^2`.
  If `e in Γ` its terms are zero anyway.

**Step 3. Co-area extraction.**
- *Level sets.* Put `A_t = {g : f(g)^2 > t}` for `t >= 0`, and `beta(A) = sum_{γ in Γ} |Aγ △ A|`. Since
  `Γ` is symmetric, `beta(A) = sum_γ sum_h |1_A(hγ) - 1_A(h)|`.
- *Co-area.* The layer-cake formula gives `int_0^inf beta(A_t) dt = sum_g sum_γ |f(g)^2 - f(gγ)^2|`.
- *Cauchy–Schwarz.* This is at most `(sum (f(g) - f(gγ))^2)^{1/2} (sum (f(g) + f(gγ))^2)^{1/2}`.
  - The first factor is at most `(4|Γ| delta ||f||^2)^{1/2}`, by Step 2.
  - The second is at most `(sum_γ sum_g 2 (f(g)^2 + f(gγ)^2))^{1/2} = (4|Γ|)^{1/2} ||f||`.
  - So `int beta(A_t) dt <= 4|Γ| sqrt(delta) ||f||^2 = 4|Γ| sqrt(delta) int_0^inf |A_t| dt`.
- *A good level.* `A_t` is nonempty exactly for `t < max f^2`. If `beta(A_t) > 4|Γ| sqrt(delta) |A_t|`
  held for all such `t`, integrating over `[0, max f^2)` would contradict the display.
  - So some nonempty `A = A_t` has `beta(A) <= 4|Γ| sqrt(delta) |A|`.
  - Hence `A` is `epsilon`-Følner, in Moore's sense `sum_γ |Aγ △ A| < epsilon |A|`, for every
    `epsilon > 4|Γ| sqrt(delta)`.

**Step 4. Size and Moore (Theorem A).**
- *Size of `A`.* `A ⊆ supp u_m`, which consists of products of `m` elements of `Γ ∪ {e}`. So
  `|A| <= (|Γ|+1)^m < (|Γ|+1)^N`.
- *The level `k*`.* Let `k* = min{ k : exp_k(0) > (|Γ|+1)^N }`. Since `exp_0(0) = 0`, `k* >= 1`. For
  `k >= 1`, `exp_k(0) > y` iff `exp_{k-1}(0) > log_2 y`, so `k* = 1 + l(N L)`.
- *Applying Moore.* `|A| < exp_{k*}(0)`. By Moore's theorem
  (`thompson-f-folner-function-exceeds-every-tower`, with the same `Γ` and `C`), `A` is not
  `C^{-k*}`-Følner. By Step 3 this forces `4|Γ| sqrt(delta) >= C^{-k*}`, i.e.
  `delta >= C^{-2k*} / (16|Γ|^2)`.
- *Conclusion.* Combined with Step 1, `-log p_{2N} >= N delta >= N C^{-2(1+l(NL))} / (16|Γ|^2)`.
  This is Theorem A.

**Step 5. Theorem B.**
- *Cocycle.* By Step 0 of `cnd-ball-growth-return-probability-proof`, `psi = ||b||^2` for a cocycle `b`.
- *The case `c = 0`.* Then `b` vanishes on `Γ`. Since `Γ` generates `F` and `b(gh) = b(g) + pi(g) b(h)`,
  `b ≡ 0`, so `psi ≡ 0`.
- *The case `c > 0`.* Item 2 of `cnd-ball-growth-bounds-return-probability-for-every-group` applies to the
  symmetric, finitely supported `mu` and gives `|B_{2cN}| >= 1/(4 p_{2N})`. Theorem A then gives
  Theorem B. If `B_{2cN}` is infinite there is nothing to prove.

**Step 6. Corollary.**
- *Tower index versus `log*`.* Let `log*` be the least `j` with `log_2^{(j)} x <= 1`. If `log* x = m`, then
  `x <= exp_{m+1}(0) < exp_{m+2}(0)`, so `l(x) <= log* x + 2`. For fixed `λ > 0` and large `R`,
  `λR <= 2^R`, so `log*(λR) <= log* R + 1`. Hence `l(λR) <= log* R + 3` for `R >= R_1(λ)`.
- *Along the sequence `R = 2cN`.* Put `h(R) = log |B_R|`. Theorem B with `λ = L/(2c)` gives
  `h(R) >= κ R C^{-2 log* R} - log 4`, where `κ = C^{-8} / (32 c |Γ|^2) > 0`.
- *Contradiction.* Suppose `h(R) <= R / g(R)` for all large `R`.
  - Along `R = 2cN -> inf` this gives `1/g(R) >= κ C^{-2 log* R} - (log 4)/R`.
  - `C^{2 log* R} = R^{o(1)}`, so the last term is at most half the middle one for large `R`.
  - Hence `g(R) <= (2/κ) C^{2 log* R}`, i.e. `log g(R) <= 2 log C · log* R + O(1)`.
  - This contradicts `log g(R) / log* R -> inf`.
