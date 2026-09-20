---
rg: 2
id: lambda-gamma-repetition-rates-capped-at-sqrt-gap-proof
kind: route
title: Compute the gap, value and a domain-wall SDP point of D(w, L), feed the SDP deficit to BHHRRS Theorem 1.2, charge against the product-strategy budget and the source gate, and read Raz--Rosen's rates off its proof
target: lambda-gamma-repetition-rates-capped-at-sqrt-gap
requires:
  - bhhrrs-xor-repetition-sdp-lower-bound
  - expansion-certified-repetition-caps-deficit-ratio
  - raz-rosen-expander-parallel-repetition-bound
---

Notation is as in the target. Indices are in `Z_L`, `L >= 3`, `w in (0, 1/2]`.
Answers are written in `{±1}`, and a check with sign `s` accepts `(a, b)` iff
`b = s a`. The cycle edge `{L−1, 0}` has `s = −1`. Every other check has
`s = +1`.

## (1) Gap

The question distribution of `D(w, L)` is

`μ(i, j) = ½[i = j]/L + ½((1 − w) C(i, j)/L + w/L²)`,

where `C(i, j) = ½` if `j = i ± 1`, and `0` otherwise. This uses `L >= 3`, so
`i+1 ≠ i−1`. Both marginals are uniform. The normalized biadjacency is
therefore `M = Lμ = ½ I + ½((1 − w) P_C + w J/L)`, where `P_C` is the cycle
walk. `M` is real symmetric, so its singular values are the absolute values of
its eigenvalues.

* On the constant vector the eigenvalue is `1`.
* On the Fourier vectors `t ≠ 0`, `J` vanishes, and the eigenvalues are
  `½ + ½(1 − w)cos(2πt/L)`. These lie in `[w/2, 1 − w/2]`.

So `σ_2 <= 1 − w/2`. The bipartite walk has spectrum `{±σ_t}`, so only its top
eigenvalue exceeds `1 − w/2`. Hence `D(w, L)` is (w/2)-gapped.

## (2) Value

Shared randomness averages deterministic strategies, so take `f, g : Z_L → {±1}`.
Let `a = Pr_i[f(i) ≠ g(i)]`. The edge part samples `(u, v, s)` with `v`
uniform. Therefore

`Pr[g(v) ≠ s f(u)] >= Pr[f(v) ≠ s f(u)] − Pr[f(v) ≠ g(v)] = Pr[f(v) ≠ s f(u)] − a`.

Around the cycle, the product of `s_e f(i) f(i+1)` is `Π s_e = −1`. So at least
one of the `L` cycle checks fails under `f`, and hence
`Pr[f(v) ≠ s f(u)] >= (1 − w)/L`. The failure probability of `(f, g)` is then at
least

`½ a + ½((1 − w)/L − a) = (1 − w)/(2L)`.

The artifact finds equality on 5 cases by brute force.

## (3) SDP point

Let `W = ceil(1/sqrt(w))` and assume `L >= W + 1`. Set `θ_i = 0` for
`0 <= i <= L − W − 1`, and `θ_(L−W−1+t) = tπ/W` for `t = 0..W`, so that
`θ_(L−1) = π`. Give both copies of question `i` the vector
`x_i = (cos θ_i, sin θ_i)`, and use the standard feasible point of
`bhhrrs-xor-repetition-sdp-lower-bound`. A check with sign `s` then costs
`(1 − s cos(θ_u − θ_v))/2`.

* **Consistency checks** cost `0`.
* **Cycle edges `{i, i+1}`, `i <= L−2`,** cost `0` off the wall. On the `W`
  wall links they cost `(1 − cos(π/W))/2 <= π²/(4W²)`.
* **The edge `{L−1, 0}`** costs `(1 + cos π)/2 = 0`.
* **Complete-layer checks** cost at most `1`, and cost `0` unless `i` or `j` is
  one of the `W` questions with `θ ≠ 0`. That happens with probability at most
  `2W/L`.

So the deficit is

`δ <= ½[(1 − w)π²/(4LW) + 2wW/L] <= π²/(8LW) + wW/L`.

Now `1/sqrt(w) <= W <= 1/sqrt(w) + 1 <= 2/sqrt(w)`. Hence
`δ <= (π²/8 + 2) sqrt(w)/L < 3.24 sqrt(w)/L`, and `sdpval >= 1 − δ`. The
artifact evaluates `δ` exactly on a grid: the worst `δ/(sqrt(w)/L)` is `1.74`.

## (4) Parametric form

Set `w = 2λ <= 1/2` and `x = (1 − 2λ)/(2γ)`, and let `L = floor(x)`.

* **Size of `x`.** From `λ <= 1/4` and `γ <= sqrt(λ/128) = sqrt(2λ)/16`, we get
  `x >= 1/(4γ) >= 4/sqrt(2λ) >= 1/sqrt(2λ) + 2`. The last step holds because
  `sqrt(2λ) <= 1/sqrt(2) < 3/2`.
* **Size of `L`.** `L >= x − 1 >= 1/sqrt(2λ) + 1`. Since `L` is an integer,
  `L >= W + 1`. Also `L >= 5 >= 3`.
* **Value.** `(1 − w)/(2L) >= (1 − w)/(2x) = γ`, so the game has
  `val <= 1 − γ`.
* **SDP.** `L >= x/2 >= 1/(8γ)`, so
  `δ < 3.24 sqrt(2λ)·8γ < 36.7 sqrt(λ) γ`.

With (1) this gives item 2.

## (5) Ceilings

Let `δ* = 37 sqrt(λ) γ`. By (4) there is `G in Γ(λ, γ)` with `sdpval(G) > 1 − δ*`.

* **(a)** BHHRRS Theorem 1.2 gives `val(G^(⊗n)) > 1 − 4 sqrt(n δ*)`, and
  `4 sqrt(37) < 25`.
* **(b)** Let `ℓ = floor(1/(64 δ*))`.
  - If `ℓ >= 1`, then `(1 − ψ)^ℓ >= val(G^(⊗ℓ)) > 1 − 4 sqrt(ℓ δ*) >= ½`.
    So `ψ < 1 − 2^(−1/ℓ) <= ln 2/ℓ`. Since `floor(y) >= y/2` for `y >= 1`,
    `ψ < 128 ln 2 · δ* < 88.8 δ* < 3300 sqrt(λ) γ`.
  - If `ℓ = 0`, then `δ* > 1/64`, and `3300 sqrt(λ)γ > 88.8/64 > 1 >= ψ`.
* **(c)** Replace alphabet `{±1}` by `{±1} × [k/2]`, and the check of sign `s`
  by the permutation `(b, c) ↦ (s b, c)`. The question distribution is
  unchanged. Take any strategy for the `n`-fold embedded game. Its projection
  to the `{±1}` coordinates satisfies every check that the strategy satisfies,
  and a lift `(f, 1)` of an XOR strategy is exact. So all repeated values are
  equal.

## (6) Route condition

A certificate valid on `Γ(λ, γ)` has `δ' >= val(G^(⊗n))`. By (5a),
`(1 − δ')² < 16·37·n sqrt(λ) γ`. The product-strategy budget of the kill claim,
`nη <= 2ε'`, then gives `C'^2 = (1 − δ')²/ε' < 1184 sqrt(λ) γ/η`. For a hard
source with `P ≠ NP`, item 1 of `expansion-certified-repetition-caps-deficit-ratio`
gives `λγ <= 1592 η`. Then `sqrt(λ)γ <= 1592 η/sqrt(λ)`, and
`1184·1592 < 1.9·10^6`.

## (7) Raz–Rosen

Take a hard source whose NO instances are biregular with value in
`(1/2, 1 − γ]` and gap `λ_G >= λ`. Both bounds of
`raz-rosen-expander-parallel-repetition-bound` decrease in `ε_G` and in `λ_G`.
For Theorem 2 this holds because `λ⁴/log(2/λ)` increases on `(0, 1]`. So the
certificate each gives is the rate at the promise `(λ, γ)`.

* **Theorem 2.** The rate is `c_P γ λ⁴/log(2/λ) <= (c_P/log 2) λ γ`, using
  `λ <= 1`. This is `Rate(0, κ)`, and item 3 of the kill gives `R <= 3184 κ`.
* **Theorem 1.** The per-round rate is `1 − (1 − γ² c(λ))^(1/log s) <= γ² c(λ)`.
  This uses Bernoulli with `1/log s <= 1`, and
  `c(λ) <= 10^−12/(32 log² 2)`. This is `Rate(K, 0)`, and item 4 of the kill
  applies.

The multigraph remark in item 5 is as stated in the target.
