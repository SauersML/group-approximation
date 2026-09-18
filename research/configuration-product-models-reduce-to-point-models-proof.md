---
rg: 2
id: configuration-product-models-reduce-to-point-models-proof
kind: route
title: A k-subset fixed-fraction sandwich plus product-action multiplicativity transfers the head-to-defect ratio from configuration models to point models, and K-tuple powers turn an unbounded Hamming ratio into a surviving head
target: configuration-product-models-reduce-to-point-models
requires:
  - jacobson-head-dies-in-gapped-finite-group-models
  - cohn-elementary-group-is-not-lef
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - experiments/configuration-point-models-2026-09-17/check_subset_fixed_fraction.py
---

Notation as on the target. For `g ∈ Sym(m)` write `b(g)` for the fraction of `[m]` that `g` moves, `F = m(1-b)` for
the number of fixed points, and `φ_k(g)` for the fraction of `Δ_k` that `g` fixes. Throughout `1 <= k` and `m >= 8k^2`,
so in particular `m >= 2k`.

## Step 1. The k-subset sandwich

**Lemma 1.** `1 - 2k b(g) <= φ_k(g) <= 1 - b(g)/2`.

*Proof.* A `g`-invariant `k`-subset is a union of cycles of `g`. Split the invariant subsets into those inside `Fix(g)`,
of which there are `binom(F,k)`, and the rest, of number `E`.

*Upper bound.* Let `c` be the number of nontrivial cycles, so `c <= bm/2`. A subset counted by `E` contains some
`t >= 1` nontrivial cycles, of total size at least `2t`, together with at most `k-2t` fixed points. Hence
```text
E <= Σ_(t>=1) binom(c,t) Σ_(s<=k-2t) binom(m,s) <= (4/3) Σ_(t>=1) binom(c,t) binom(m,k-2t),
```
since `binom(m,j-1)/binom(m,j) = j/(m-j+1) <= 2k/m <= 1/4` for `j <= k`. The same ratio gives
`binom(m,k-2t)/binom(m,k) <= (2k/m)^(2t)`, so
```text
E / binom(m,k) <= (4/3) Σ_(t>=1) (bm/2)^t (4k^2/m^2)^t = (4/3) Σ_(t>=1) x^t,   x = 2bk^2/m <= b/4 <= 1/4,
```
which is at most `(4/3)(4/3)(b/4) = 4b/9 <= b/2`. Also `binom(F,k)/binom(m,k) <= (F/m)^k <= 1-b`. Adding the two gives
`φ_k <= 1 - b/2`.

*Lower bound.* 
```text
φ_k >= binom(F,k)/binom(m,k) = Π_(i<k) (1 - (m-F)/(m-i)) >= 1 - k bm/(m-k) >= 1 - 2kb.
```
If `F < k` the product is `0`, but then `bm > m-k`, so `2kb > 1` and the bound is trivial. ∎

The script `experiments/configuration-point-models-2026-09-17/check_subset_fixed_fraction.py` counts invariant subsets
exactly, as the `x^k` coefficient of `Π_j (1+x^j)^(c_j)`, and checks both inequalities on random and adversarial cycle
types for `k = 1..4` and `m >= 8k^2`. Output: `tests=1578 violations=0`.

## Step 2. Tops

An element `g = (g_1, ..., g_l; π)` of `S_m wr S_l` sends `(A_i)_i` to `(g_i A_(π^(-1) i))_i`. Suppose `π ≠ 1` and `i`
lies on a cycle of `π` of length at least `2`. A fixed tuple then has `A_i = g_i A_(π^(-1) i)`, so `A_i` is determined
by the other coordinates. The fixed fraction is therefore at most `1/|Δ_k| <= 1/m`, because `binom(m,k) >= m` for
`1 <= k <= m-1`. This is part 1 of Theorem CP.

## Step 3. Ratio transfer for trivial tops

Let `w` have trivial top, so `σ(w) = (w_1, ..., w_l; 1)`. It fixes `(A_i)` iff each `w_i` fixes `A_i`, so the fixed
fraction on `Δ_k^l` is `Π_i φ_k(w_i)`. On `[m] x [l]` the point model has `h_pt(w) = (1/l) Σ_i b(w_i)`. By Lemma 1:
```text
h_σ(z)   = 1 - Π φ_k(z_i) <= Σ (1 - φ_k(z_i)) <= 2k Σ b(z_i) = 2kl h_pt(z),
δ_σ(r)   = 1 - Π φ_k(r_i) >= 1 - Π (1 - b(r_i)/2) >= 1 - exp(-l δ_pt(r)/2) >= (1 - 1/e) min(1, l δ_pt(r)/2).
```
The last inequality is concavity of `1 - e^(-x)` on `[0,1]`. Take `r` with `δ_pt(r) = δ_pt`.
- If `l δ_pt >= 2`, then `h_σ/δ_σ <= 1/(1-1/e) = e/(e-1)`.
- Otherwise `h_σ/δ_σ <= 2kl h_pt / ((1-1/e) l δ_pt/2) = (e/(e-1)) 4k h_pt/δ_pt`.

This is (CP). Nothing depends on `l`.

## Step 4. Theorem HD

The direction (b) ⇒ (a) is immediate. For (a) ⇒ (b), assume (b) fails. Then for every `n` there is a Hamming model
`σ_n` on some `Ω_n` with `h_n := h_(σ_n)(z) > n δ_(σ_n, R_n)`. Since `h_n <= 1`, `δ_(σ_n,R_n) < 1/n`.

Put `K = ⌈1/h_n⌉` and let `τ_n` be the diagonal action of `σ_n` on `Ω_n^K`. A word `w` fixes a tuple iff it fixes
every coordinate, so `τ_n` moves the fraction `1 - (1 - h_(σ_n)(w))^K` of the tuples. Hence:
```text
δ_(τ_n)(r) <= K δ_(σ_n)(r) <= (1/h_n + 1) δ_(σ_n)(r) <= 2 δ_(σ_n)(r)/h_n < 2/n        (r ∈ R_n),
h_(τ_n)(z) >= 1 - exp(-K h_n) >= 1 - 1/e.
```
For each fixed `j` we have `R_j ⊂ R_n` once `n >= j`, so `δ_(τ_n, R_j) -> 0` while the head stays at least `1 - 1/e`.
This contradicts (a). ∎

## Step 5. The corollary for the Jacobson head

Let `σ_n` be configuration models of type `(m_n, k_n, l_n)` with `m_n >= 8k_n^2`, relator defects `δ_n -> 0` on every
window, and `h_(σ_n)(z) >= c > 0`.

**Tops are trivial.** Fix a window `R_j` that contains a finite presentation of `St_4(J)`
(`steinberg-finite-presentation-and-kazhdan-theorem`). Once `δ_n < 1 - 1/m_n`, Step 2 shows that every relator of
`R_j` has trivial top. So the tops define a homomorphism `ρ : St_4(J) = EL_4(J) -> S_(l_n)`.
- `ker ρ` meets the finitary kernel `L_4 = GL_fin(N x {1..4}, F_2)` in a normal subgroup of finite index.
- `L_4` is infinite and its commutator subgroup is simple, so this intersection contains `[L_4, L_4]`.
- The head `z = x_13(Q)` is a transvection, hence a commutator in `L_4`, so `ρ(z) = 1`.

The same kill is the pigeonhole Steinberg chain of `jacobson-head-dies-in-gapped-finite-group-models`. It is also why
`EL_4(J)` is not LEF (`cohn-elementary-group-is-not-lef`). So `z` has trivial top, and Step 3 applies.

**Ratio blow-up.** From Step 3, `2k_n l_n h_pt >= h_(σ_n)(z) >= c`. Once `δ_n < 1 - 1/e`, the lower bound on `δ_σ` forces
`l_n δ_pt <= 2δ_n/(1 - 1/e)`. Dividing:
```text
h_pt / δ_pt >= c (1 - 1/e) / (4 k_n δ_n).
```
This tends to infinity **provided `k_n δ_n -> 0`**, which is automatic when `k_n` is bounded. Under that hypothesis the
point models `σ_(n,pt)` on `[m_n] x [l_n]` violate (b) of Theorem HD for every window. By Step 4, their `K`-tuple powers
are Hamming models with defect `-> 0` on every window and head at least `1 - 1/e`.

Conversely, a Hamming model on `[m]` with `m >= 8` is a configuration model of type `(m,1,1)`. Small sets can be
replaced by tuple powers first. So, for configuration sequences with `k_n δ_n -> 0`, configuration models see the head
iff Hamming point models do.

## Scope

Lemma 1 is the only place where `m >= 8k^2` is used. For `sqrt(m/8) < k = o(m)`, the count `E` of invariant subsets
that are not pointwise fixed is no longer dominated by `b binom(m,k)`. A permutation with many 2-cycles has about
`binom(c, k/2)` invariant subsets made of whole 2-cycles. The ratio `h/δ` can then genuinely change, and this range is
not covered. Neither are branch (P) (primitive irreducible representations) or non-permutation unitary models.
