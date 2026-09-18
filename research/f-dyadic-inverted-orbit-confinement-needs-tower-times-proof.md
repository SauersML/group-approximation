---
rg: 2
id: f-dyadic-inverted-orbit-confinement-needs-tower-times-proof
kind: route
title: Take the square of the walk's power at a good return ratio, project onto root-switch invariant functions, union independent samples to cover the breakpoints, and apply the tower-size witness theorem
target: f-dyadic-inverted-orbit-confinement-needs-tower-times
requires: [thompson-f-dyadic-ea-witnesses-need-tower-size]
---

Notation as in the claim. `F` acts on `D` by homeomorphisms and on `P_f(D)` by `g·A = gA`. The lamplighter
`L = (Z/2)^{(D)} ⋊ F` acts by `(φ, g)·A = φ Δ gA`, and `δ ∈ L` switches the lamp at `y = 1/2`, so `δ·A = A Δ {y}`.

**The imported theorem** (`thompson-f-dyadic-ea-witnesses-need-tower-size`, ESTABLISHED). For `s ∈ F`, `B(s)` is its
breakpoint set and `β(s)` its log₂-slope jumps; `L_Γ = Σ_{s∈Γ} ‖β(s)‖₁`. Let `ν` be a finitely supported
probability measure on `P_f(D)`, `k = max{|S| : S ∈ supp ν}`, `ε₁ = Σ_{s∈Γ} ‖sν − ν‖₁` with `(sν)(T) = ν(s⁻¹T)`,
and `ε₂ = Σ_{s∈Γ} Σ_{y'∈B(s)} ν{S : y' ∉ S}`. If `ε₁ + 2ε₂ < C^{−m}/2` for some `m ≥ 1`, then
`|supp ν| · (4 L_Γ C^m + 3)^k ≥ exp_m(0)`.

**The generators.** `x_0` has slopes `1/2, 1, 2` on `[0,1/2], [1/2,3/4], [3/4,1]`, so `B(x_0) = {1/2, 3/4}` and
`‖β(x_0)‖₁ = 2`; `B(x_0⁻¹) = {1/4, 1/2}`. `x_1` is the identity on `[0,1/2]` and has slopes `1/2, 1, 2` on
`[1/2,3/4], [3/4,7/8], [7/8,1]`, so `B(x_1) = {1/2, 3/4, 7/8}` and `‖β(x_1)‖₁ = 3`; `B(x_1⁻¹) = {1/2, 5/8, 3/4}`.
Hence `L_Γ = 10`, and `b := Σ_{s∈Γ} |B(s)| = 10`. Every breakpoint `y'` is `w y` for a word `w` in `Γ` of length
`ℓ(y') ≤ 2`: `1/4 = x_0(1/2)`, `3/4 = x_0⁻¹(1/2)`, `5/8 = x_1(3/4)`, `7/8 = x_1⁻¹(3/4)`.

## Step 0. The return probability is `E 2^{−|O_n|}`

Let `π` be the permutation representation of `L` on `ℓ²(P_f(D))`, `(π(ℓ)f)(A) = f(ℓ⁻¹·A)`, and
`P = π(ν_y) = Λ M Λ` with `Λ = (I + π(δ))/2` and `M = (1/5)(I + Σ_{s∈Γ} π(s))`. Since `π(δ)` is a self-adjoint
involution, `Λ` is an orthogonal projection; since `Γ` is symmetric, `M` is self-adjoint. So `P` is self-adjoint,
and `⟨P^n δ_∅, δ_∅⟩ = ν_y^{∗n}{ℓ : ℓ·∅ = ∅} =: p_n`.

A step of the walk is `ℓ_k = δ^{ε'_k} h_k δ^{ε_k}` with `ε_k, ε'_k` fair bits and `h_k ∼ μ`, all independent. Put
`A_k = ℓ_k⋯ℓ_1·∅` and `{z}^1 = {z}`, `{z}^0 = ∅`. Then `A_k = {y}^{ε'_k} Δ {h_k y}^{ε_k} Δ h_k A_{k−1}`, and applying
`g_k⁻¹ = g_{k−1}⁻¹h_k⁻¹`,

`g_k⁻¹A_k = g_{k−1}⁻¹A_{k−1} Δ {g_{k−1}⁻¹y}^{ε_k} Δ {g_k⁻¹y}^{ε'_k}`.

So `g_n⁻¹A_n = Δ_{k=1}^n ({g_{k−1}⁻¹y}^{ε_k} Δ {g_k⁻¹y}^{ε'_k})`. Condition on `(h_k)`. A point outside `O_n` is never
in this set. For `z ∈ O_n`, `z ∈ g_n⁻¹A_n` iff the sum of the bits attached to `z` is odd, where `ε_k` is attached to
`g_{k−1}⁻¹y` and `ε'_k` to `g_k⁻¹y`. Distinct points have disjoint sets of bits, and each `z = g_j⁻¹y ∈ O_n` has at
least one (`ε_{j+1}` if `j < n`, `ε'_n` if `j = n ≥ 1`). Parities of disjoint nonempty sets of independent fair bits
are independent fair bits. Hence `P(A_n = ∅ | (h_k)) = 2^{−|O_n|}` and `p_n = E 2^{−|O_n|}` for `n ≥ 1`. Also
`p_{2k} = ‖P^kδ_∅‖² > 0`, since `ν_y(e) > 0`.

## Step 1. A good return ratio gives a small Dirichlet ratio

`Σ_{s∈Γ} π(s)` is a sum of four self-adjoint contractions, so it is `≥ −4I`, and `M ≥ −(3/5)I`. For any `f`,
`⟨Pf, f⟩ = ⟨MΛf, Λf⟩ ≥ −(3/5)‖Λf‖² ≥ −(3/5)‖f‖²`. So `I + P ≥ (2/5)I`. The operators `I − P ≥ 0` and `I + P` commute,
hence `I − P² = (I − P)(I + P) ≥ (2/5)(I − P)`.

Fix `η ∈ (0, 1/5]` and `n ≥ 1`, and suppose `p_{2n} ≥ e^{−ηn}`. Since `p_0 = 1`, the product of the `n` ratios
`p_{2k+2}/p_{2k}`, `0 ≤ k < n`, is at least `e^{−ηn}`, so some `k < n` has `p_{2k+2} ≥ e^{−η} p_{2k}`. Put
`f = P^kδ_∅`. Then `‖f‖² = p_{2k}` and

`⟨(I − P)f, f⟩ ≤ (5/2)⟨(I − P²)f, f⟩ = (5/2)(p_{2k} − p_{2k+2}) ≤ (5/2)(1 − e^{−η}) p_{2k} ≤ (5/2) η ‖f‖²`.

The entries of `f` are nonnegative, and `f` is supported on configurations reached in `k` steps.

## Step 2. Projecting onto root-switch invariant functions gives a witness measure

Put `g = Λf ≥ 0`. Since `Λ` is a self-adjoint projection and `M ≤ I`,

`⟨(I − P)f, f⟩ = ‖f‖² − ⟨MΛf, Λf⟩ = (‖f‖² − ‖g‖²) + ⟨(I − M)g, g⟩`,

and both brackets are `≥ 0`. So `‖g‖² ≥ (1 − 5η/2)‖f‖² ≥ ‖f‖²/2 > 0` and `⟨(I − M)g, g⟩ ≤ (5/2)η‖f‖² ≤ 5η‖g‖²`. Since
`Γ` is symmetric, `⟨(I − M)g, g⟩ = (1/5) Σ_{s∈Γ} (‖g‖² − ⟨π(s)g, g⟩) = (1/10) Σ_{s∈Γ} ‖π(s)g − g‖²`, so

`Σ_{s∈Γ} ‖π(s)g − g‖² ≤ 50 η ‖g‖²`.

Let `ν = g²/‖g‖²`, a probability measure on `P_f(D)`, and `e := 29√η`.

*(a) Invariance defect.* `(sν)(T) = ν(s⁻¹T) = (π(s)g)(T)²/‖g‖²`. By Cauchy–Schwarz,
`‖sν − ν‖₁ = ‖(π(s)g − g)(π(s)g + g)‖₁/‖g‖² ≤ 2‖π(s)g − g‖/‖g‖`, and summing over the four `s`,
`ε₁(ν) ≤ 2 · 2 (Σ_s ‖π(s)g − g‖²)^{1/2}/‖g‖ ≤ 4√(50η) ≤ e`.

*(b) The root is covered half the time.* `π(δ)g = g`, i.e. `g(A Δ {y}) = g(A)`. The involution `A ↦ A Δ {y}`
exchanges `{y ∉ A}` and `{y ∈ A}`, so `ν{S : y ∉ S} = 1/2` exactly.

*(c) Every breakpoint is covered almost half the time.* Let `y' ∈ ∪_s B(s)`, `y' = w y` with `w = s_ℓ⋯s_1`,
`s_i ∈ Γ`, `ℓ ≤ 2` and distinct letters (Generators paragraph: `1/4 = x_0 y`, `3/4 = x_0⁻¹y`, `5/8 = x_1x_0⁻¹y`,
`7/8 = x_1⁻¹x_0⁻¹y`). Then `y' ∈ S` iff `y ∈ w⁻¹S`, so `ν{y' ∉ S} = (w⁻¹ν){T : y ∉ T}`. By the triangle inequality
and translation invariance of `‖·‖₁`, `‖w⁻¹ν − ν‖₁ ≤ Σ_{i} ‖s_i⁻¹ν − ν‖₁ ≤ ε₁(ν)` (the `s_i⁻¹` are distinct elements of
`Γ`). An event changes probability by at most half the `ℓ¹` distance, so `ν{y' ∉ S} ≤ 1/2 + e`.

*(d) Size.* One step `ℓ = δ^{ε'}hδ^{ε}` takes at most `2 · 5 · 2 = 20` values and changes `|A|` by at most `2`. So
`|supp f| ≤ 20^k` with sets of size `≤ 2k`, and `supp g ⊆ supp f ∪ δ·supp f` has at most `2 · 20^k` elements, of size
`≤ 2k + 1`. With `K := k + 1 ≤ n`: `|supp ν| ≤ 40^K` and every `S ∈ supp ν` has `|S| ≤ 2K`.

## Step 3. A union of `r` independent samples covers the breakpoints

Assume `e ≤ 1/8`. For `r ≥ 1` let `ν_r` be the law of `S_1 ∪ ⋯ ∪ S_r` with `S_i` i.i.d. `∼ ν`, i.e. the push-forward of
`ν^{⊗r}` under the union map `U`. `U` is `F`-equivariant, so `sν_r = U_*((sν)^{⊗r})` and

- `ε₁(ν_r) ≤ Σ_s ‖(sν)^{⊗r} − ν^{⊗r}‖₁ ≤ r ε₁(ν) ≤ r e` (telescoping one coordinate at a time);
- `ν_r{y' ∉ S} = ν{y' ∉ S}^r ≤ (1/2 + e)^r ≤ (5/8)^r` for every breakpoint `y'`, so `ε₂(ν_r) ≤ b (5/8)^r = 10 (5/8)^r`;
- `|supp ν_r| ≤ |supp ν|^r ≤ 40^{Kr}`, and every set in `supp ν_r` has at most `2Kr` elements.

## Step 4. Parameters: item 1

Fix `m ≥ 1` and take `r = r_m`, `η = η_m`. Then `(8/5)^{r_m} ≥ 80 C^m`, so `2ε₂(ν_r) ≤ 20 (5/8)^{r_m} ≤ C^{−m}/4`; and
`√η_m = C^{−m}/(117 r_m)`, so `ε₁(ν_r) ≤ 29 r_m √η_m = (29/117) C^{−m} < C^{−m}/4`. Also `r_m ≥ 10` (as
`log₂80/log₂(8/5) > 9.3`), so `e = 29/(117 r_m C^m) < 1/8` and `η_m < 1/5`. Hence `ε₁(ν_r) + 2ε₂(ν_r) < C^{−m}/2`, and the
imported theorem with `L_Γ = 10` gives

`40^{K r_m} (40 C^m + 3)^{2K r_m} ≥ |supp ν_r| (4 L_Γ C^m + 3)^{max |S|} ≥ exp_m(0)`.

Taking `log₂`: `K r_m log₂(40 (40C^m + 3)²) ≥ exp_{m−1}(0)`, i.e. `K ≥ N_m`, so `n ≥ K ≥ N_m`.

We have shown: if `n ≥ 1` and `p_{2n} ≥ exp(−η_m n)`, then `n ≥ N_m`. This is item 1.

## Step 5. The log-star form: item 2

`N_m → ∞`, so `m(n)` exists, and item 1 with `m = m(n)` gives `p_{2n} < exp(−η_{m(n)} n)`. Since `r_m ≤ a_C m` and
`log₂(40(40C^m + 3)²) ≤ a_C m` for a constant `a_C`, `N_m ≥ exp_{m−1}(0)/(A m²)` with `A = a_C²`. Let
`l(x) = min{j : exp_j(0) > x}` and `m* = l(n) + 2`. Then `exp_{m*−2}(0) > n`, so `exp_{m*−1}(0) > 2^n` and
`N_{m*} > 2^n/(A (l(n) + 2)²) > n` once `n ≥ n_0(C)`, as `l(n) ≤ n`. Hence `m(n) ≤ l(n) + 2` for `n ≥ n_0(C)` and
`m(n) ≤ m(n_0)` below, so `m(n) ≤ l(n) + O_C(1) = log* n + O_C(1)` (if `log₂^{(j)} n ≤ 1` then
`n ≤ exp_{j+1}(0)`, so `l(n) ≤ log* n + 2`). Substituting into `η_m = C^{−2m}/(117 r_m)²` with `r_m = O_C(m)` gives the
displayed rate.

## Step 6. First confinement times: item 3

Let `ε > 0`, `N ≥ 1`, `P(|O_N| < εN) > e^{−εN}`, and `m ≥ 1` with `8ε ≤ η_m`. Since `y ∈ O_N`, `|O_N| ≥ 1`, so the event
is nonempty only if `εN > 1`; thus `N > 1/ε ≥ 8/η_m`. On the event, `2^{−|O_N|} ≥ 2^{−εN}`, so
`p_N ≥ e^{−(1 + ln 2)εN} ≥ e^{−1.7εN}`. Put `n' = ⌈N/2⌉ ≥ 1`, so `2n' ∈ {N, N+1}`. Since `|O_{N+1}| ≤ |O_N| + 1`,
`p_{2n'} ≥ p_N/2 ≥ (1/2) e^{−3.4 ε n'}`. Now `(η_m − 3.4ε) n' ≥ 0.575 η_m · N/2 > 0.575 · 4 > ln 2`, so
`p_{2n'} ≥ e^{−η_m n'}`. By item 1, `n' ≥ N_m`, and `N ≥ 2n' − 1 ≥ 2N_m − 1`.

## Step 7. Sizes quoted in the Reading and the class kill

- *The level `m(ε)`.* `η_m ≥ C^{−2m}/(A' m²)` with `A' = (117 a_C)²`, so every `m` with `C^{2m} A' m² ≤ 1/(8ε)`
  satisfies `8ε ≤ η_m`. The largest such `m` is `½ log_C(1/ε) − O_C(log log(1/ε))`.
- *The time.* `N_m ≥ 2^{exp_{m−2}(0)}/(A m²) > exp_{m−2}(0)` once `m ≥ m_0(C)`, since `exp_{m−2}(0) ≥ 2^{m−4}` for
  `m ≥ 5`. So `2N_m − 1 > exp_{m−2}(0)`.
- *Profiles.* If `p_n ≥ exp(−n/g(n))` along infinitely many `n` with `log g(n)/log* n → ∞`, then for even `n = 2n''`
  (or `n = 2n'' − 1`, via `p_{2n''} ≥ p_{2n''−1}/2`) item 2 gives `1/g(n) ≥ η_{m(n'')}/2 − O(1/n)`, i.e.
  `log g(n) ≤ 2 log* n · log C + O_C(log log* n)`, a contradiction. For a bounded-complexity event `E_n` the bound
  `E[2^{−|O_n|}; E_n] ≤ p_n` transfers the same obstruction.
- *Why the kill does not decide the hole.* The hole needs a zero exponential rate along some sequence of times. Item 2
  allows rates `C^{−2 log* n}`, which tend to `0`; nothing here excludes confinement at times beyond every fixed tower.
