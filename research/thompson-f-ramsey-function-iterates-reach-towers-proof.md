---
rg: 2
id: thompson-f-ramsey-function-iterates-reach-towers-proof
kind: route
title: Invert Følner sets to match conventions, feed k of order Cⁿ into Towsner's inequality, and compare fixed-height towers with Moore's tower
target: thompson-f-ramsey-function-iterates-reach-towers
requires: [moore-ramsey-criterion-for-amenability, thompson-f-folner-function-exceeds-every-tower]
---

Notation is as in the claim. `Føl_S` is Moore–Towsner's function, with the left, summed convention
`Σ_{a∈S}|aB △ B| ≤ |B|/k`. The tower theorem (`thompson-f-folner-function-exceeds-every-tower`, arXiv:0905.1118)
uses the right, summed, strict convention: `A` is ε-Følner w.r.t. `Γ` if `Σ_{γ∈Γ}|Aγ △ A| < ε|A|`.

**Step 0 (basic properties of `R`).** By the two facts in `moore-ramsey-criterion-for-amenability`:
- `R(m) < ∞` for every `m`, since `F` is amenable;
- `R` is nondecreasing;
- `R(m) ≥ m`.

Hence `j ↦ R^j(1)` is nondecreasing, and `R^j ≥ R^{j′}` pointwise for `j ≥ j′`.

**Step 1 (convention change).** Claim: if `B` is `1/k`-Følner in the left convention w.r.t. `S` and `k > 2Cⁿ`, then `A = B⁻¹`
is `C^{−n}`-Følner in the right convention w.r.t. `Γ`. In particular `|B| = |A| ≥ exp_n(0)`.
- For `x ∈ S`, `Ax⁻¹ = (xB)⁻¹`, so `|Ax⁻¹ △ A| = |xB △ B|`.
- `Ax = (x⁻¹B)⁻¹`, and left multiplication by `x` gives `|x⁻¹B △ B| = |B △ xB|`.
- Therefore `Σ_{γ∈Γ}|Aγ △ A| = 2Σ_{x∈S}|xB △ B| ≤ 2|A|/k < C^{−n}|A|`.

So `Føl_S(k) ≥ exp_n(0)` whenever `k > 2Cⁿ`.

**Step 2 (Theorem A).** Apply Theorem 3.2 with `s = 2`, `k = k_n` and `p = p_n`. The hypothesis
`(3/4)^{p_n} < 1/(4k_n) = 1/(2ks)` holds by the choice of `p_n`. Since `k_n > 2Cⁿ`, Step 1 gives

`exp_n(0) ≤ Føl_S(k_n) ≤ 5^{R^{2p_n}(1)} = 5^{R^{j_n}(1)}`.

Take `log₂`: `exp_{n−1}(0) ≤ log₂5 · R^{j_n}(1)`. Step 0 extends this to all `j ≥ j_n`.

The bounds on `j_n` in the claim follow from `8Cⁿ < 4k_n ≤ 8Cⁿ + 4 ≤ 12Cⁿ` together with
`(4/3)^{p_n−1} ≤ 4k_n < (4/3)^{p_n}`.

**Step 3 (two tower facts).**
- (T1) For integers `a ≥ 0` and reals `x, y ≥ 0` with `y` an integer, `exp_a(x) + y ≤ exp_a(x + y)`. Induct on `a`.
  The case `a = 0` is an equality. For the step, `2^z + y ≤ 2^{z+y}` for `z ≥ 0`, because
  `2^z(2^y − 1) ≥ 2^y − 1 ≥ y`. So `exp_{a+1}(x) + y ≤ 2^{exp_a(x)+y} ≤ exp_{a+1}(x+y)`.
- (T2) `exp_m(0) ≥ 2^{m−2}` for `m ≥ 1`. The first values are 1, 2, 4, 16, and the induction uses `2^{m−2} ≥ m − 1`.
  Hence for fixed `h` and constants `a, b`, the inequality `exp_n(0) ≤ exp_h(an + b)` fails for all large `n`.
  - When `n ≥ h + 2`, `exp_n(0) = exp_h(exp_{n−h}(0))` and `exp_h` is strictly increasing, so the
    inequality would force `exp_{n−h}(0) ≤ an + b`.
  - That contradicts (T2).

**Step 4 (Corollary B).** Suppose `R(m) ≤ exp_q((log_q m)^d)` for all `m ≥ M`, where `log_q M ≥ 2`. Put
`L = (log_q M)^d ≥ 2` and `y_j = log_q max(R^j(1), M)`.
- If `R^j(1) ≥ M`, then `R^{j+1}(1) ≤ exp_q(y_j^d)`, so `y_{j+1} ≤ max(y_j^d, log_q M) = y_j^d`.
- If `R^j(1) < M`, then Step 0 gives `R^{j+1}(1) ≤ R(M) ≤ exp_q(L)`, so `y_{j+1} ≤ L`.

In both cases `y_{j+1} ≤ max(y_j, L)^d`. Since `y_0 = log_q M ≤ L`, induction gives `y_j ≤ L^{d^j}`.
Write `L^{d^j} = exp_2(j log₂d + λ)` with `λ = log₂log₂L ≥ 0`. Then
`R^j(1) ≤ exp_{q+2}(j log₂d + λ)`. Take `j = j_n ≤ an + b`, with `a, b` from the claim.
- Theorem A gives `exp_{n−1}(0)/log₂5 ≤ exp_{q+2}((an+b) log₂d + λ)`.
- For `n ≥ 5`, the left side is at least `exp_{n−2}(0)`, since `2^x ≥ x log₂5` for `x ≥ 4`.
- So `exp_{n−2}(0) ≤ exp_{q+2}(a′n + b′)` for all large `n`, which contradicts (T2).

**Step 5 (Proposition C).** Let `(3/4)^p < 1/(4k)` and `2Cⁿ < k`. Then `(4/3)^p > 4k > 8Cⁿ`, so `p > n ln C/ln(4/3)`.
With `r ≥ ln(4/3)/(2 ln C)` this gives `2pr > n`. Hence
`5^{Q^{2p}(1)} ≥ Q^{2p}(1) = exp_{2pr}(1) ≥ exp_n(0)`.
Step 1 only yields `Føl_S(k) ≥ exp_n(0)` for `k > 2Cⁿ`, and Theorem 3.2 only yields `Føl_S(k) ≤ 5^{R^{2p}(1)}`.
So the constraint these two imports place on `R` is satisfied by `R = Q`.

**Step 6 (Proposition D).** Assume AMP(D). Suppose for contradiction that `R(m) ≤ exp_q(m)` for all `m`. Put `P = 2D + q`.

*The one-function bound.* For integers `m, u ≥ 1`, (T1) and monotonicity of the towers give
`R̃(m, 1/u) ≤ exp_D(exp_q(exp_D(m+u)) + u) ≤ exp_D(exp_q(exp_D(m+u) + u)) ≤ exp_{D+q}(exp_D(m+2u)) = exp_P(m+2u)`.

*Two functions.* Let `u = 4k`. The quoted composition inequality with `l = 2` gives
`R̃(1, 1/u, 2) ≤ R̃(R̃(1, 1/u), 1/u) ≤ exp_P(R̃(1,1/u) + 2u) ≤ exp_P(exp_P(1+2u) + 2u) ≤ exp_{2P}(1+4u)`.
The bound applies at `m = R̃(1,1/u) ≥ 1`, because `F` is infinite, so `B_1ν ⊆ B_n` needs `n ≥ 1`.

*Følner.* Proposition 3.1 with `m = 1`, `ε = 1/(4k)` and `|S| = 2` gives `F_{F,S}(1, 1/k) ≤ R̃(1, 1/(4k), 2)`. The quoted
inequality `Føl_S(k) ≤ 5^{F_{F,S}(1,1/k)}` then gives
`Føl_S(k) ≤ 5^{exp_{2P}(1+16k)} ≤ 2^{3·exp_{2P}(1+16k)} ≤ exp_{2P+1}(3+48k)`.
- The last step uses `3·exp_a(z) ≤ exp_a(3z)` for `z ≥ 1`. The case `a = 0` is an equality. For `a ≥ 1`,
  `3·2^{exp_{a−1}(z)} ≤ 2^{exp_{a−1}(z)+2} ≤ 2^{exp_{a−1}(z+2)} ≤ 2^{exp_{a−1}(3z)}` by (T1).

*Contradiction.* Take `k = k_n ≤ 3Cⁿ`. Step 1 gives `exp_n(0) ≤ exp_{2P+1}(3 + 144Cⁿ) ≤ exp_{2P+2}(an + b)` for constants
`a, b`. This contradicts (T2) for large `n`. So for every `q` some `m` has `R(m) > exp_q(m)`. Every Kalmár-elementary
function is bounded by some fixed `exp_q`, so `R` is not elementary.

**Step 7 (where the tower is lost).** In Moore's proof of (3⇒4) of Theorem 2.1, precision `q^n < ε` is obtained from a
chain `B_0 = A ⊆ B_1 ⊆ ⋯ ⊆ B_n` in which each `B_{i+1}` is Ramsey for `B_i`. So `R̃(m, ε) ≤ R^p(m)` with
`p = Θ(log 1/ε)`, and Theorem 3.2 inherits exactly this composition depth. Theorem A is the image of Moore's tower
under that depth. AMP(D) is the statement that the depth can be traded for a bounded number of exponentials. That
trade is exactly what separates Proposition C from Proposition D.
