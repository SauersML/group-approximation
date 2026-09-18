---
rg: 2
id: subset-models-are-point-models-at-every-size-proof
kind: route
title: Disjoint pairs {x, gx} that an invariant subset cannot split give a two-sided k-subset displacement bound at every size, so product action rescales head and defect by the same factor k'l, and tuple powers turn an unbounded Hamming ratio into a surviving head
target: subset-models-are-point-models-at-every-size
requires:
  - cohn-elementary-group-is-not-lef
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - experiments/subset-displacement-all-sizes-2026-09-17/check_two_sided_subset_displacement.py
---

Notation as on the target. For `g ∈ S_m` let `D(g)` be the set of moved points, `M = |D(g)|` and `b = M/m`. `X` denotes a
uniformly random `k`-subset of `[m]`, `1 <= k <= m-1`, and `μ_k(g) = P(gX ≠ X)`. Put `k' = min(k, m-k)`.

## Step 1. Lemma D

**Complement symmetry.** The complement map `X -> [m] \ X` is a bijection `Δ_k -> Δ_(m-k)` that commutes with the action
of `S_m`. So `μ_k = μ_(m-k)`, and it suffices to prove (D) for `k <= m/2`, where `k' = k`. If `M = 0`, both sides of (D)
are `0`. Assume `M >= 2`.

**Upper bound.** If `X ∩ D(g) = ∅`, then `g` fixes `X` pointwise. So
`μ_k(g) <= P(X ∩ D(g) ≠ ∅) <= Σ_(x ∈ D(g)) P(x ∈ X) = M k/m = k b`, and trivially `μ_k(g) <= 1`.

**Disjoint pairs.** Write each nontrivial cycle of `g` as `(x_1 x_2 ... x_L)` with `L >= 2`. The pairs
`{x_1,x_2}, {x_3,x_4}, ...` are `floor(L/2) >= L/3` disjoint pairs of the form `{x, gx}`. Collecting them over all cycles
gives `r >= M/3` pairwise disjoint pairs `{x, gx}`. Let `U` be their union, with `u = |U| = 2r >= 2M/3` and `u >= 2`.

**Invariant subsets do not split pairs.** Suppose `gX = X`, and let `{x, gx}` be one of the pairs. If `x ∈ X` then
`gx ∈ gX = X`. If `gx ∈ X` then `x = g^(-1)(gx) ∈ g^(-1)X = X`. So `X ∩ U` is a union of pairs.

**Conditioning on `t = |X ∩ U|`.** Given `t`, the set `X ∩ U` is a uniform `t`-subset of `U`. It is a union of pairs
with probability `0` for odd `t`, and with probability `f(j) = binom(r,j)/binom(2r,2j)` for `t = 2j`. Now
```text
f(j+1)/f(j) = (2j+1)/(2r-2j-1),
```
so on `0 <= j <= r` the function `f` decreases while `j < (r-1)/2` and then increases, and `f(j) = f(r-j)`. Therefore,
for `1 <= j <= r-1`, `f(j) <= f(1) = 1/(2r-1)`, which is at most `1/3` when `r >= 2`. When `r = 1` the only proper value
is `t = 1`, where the probability is `0`. In all cases
```text
P(gX = X  |  1 <= t <= u-1)  <=  1/3,     so     μ_k(g) >= (2/3) P(1 <= t <= u-1).
```

**The two extreme events.** Put `x = k u/m`.
- `P(t = 0) = binom(m-u,k)/binom(m,k) = Π_(i<k) (m-u-i)/(m-i) <= (1 - u/m)^k <= e^(-x)`. The product is `0` if
  `m - u < k`.
- `P(t = u) = binom(m-u,k-u)/binom(m,k) = Π_(i<u) (k-i)/(m-i) <= (k/m)^u`. Since `u >= 2` and `k/m <= 1/2`,
  `(k/m)^u <= (k/m)^2 <= k/(2m) <= x/4`, and also `(k/m)^u <= 1/4`. So `P(t = u) <= min(1,x)/4`.

Using `1 - e^(-x) >= (1 - 1/e) min(1,x)`:
```text
P(1 <= t <= u-1) >= 1 - e^(-x) - min(1,x)/4 >= (3/4 - 1/e) min(1,x) >= 0.382 min(1,x).
```

**Conclusion.** `x = k u/m >= (2/3) k b`, so `min(1,x) >= (2/3) min(1, k b)`. Hence
```text
μ_k(g) >= (2/3)(0.382)(2/3) min(1, k b) >= 0.169 min(1, k b) >= min(1, k b)/6.   ∎
```

**Check.** `experiments/subset-displacement-all-sizes-2026-09-17/check_two_sided_subset_displacement.py` counts invariant
`k`-subsets exactly, as the `x^k` coefficient of `Π_(cycles) (1 + x^len)`. It covers:
- every cycle type of every `m <= 26`, at every `k`;
- adversarial types up to `m = 600`: many 2-cycles or 3-cycles, one long cycle, two half cycles, and random types;
- the sizes `k ∈ {1, 2, 3, sqrt(m/8), sqrt(m), 2 sqrt(m), m/10, m/4, m/3, m/2, m - sqrt(m), m-1}`, which include the range
  left open by Theorem CP.

Output:
```text
lemma tests=253908 (exhaustive m<=26: 251910) violations=0
worst mu/min(1,k'b) = 0.5008 at (m,k,cycles)=(600, 300, [2, 1, 1, 1, 1, 1, 1, 1])
ratio-transfer tests=396 violations=0 worst (h_c/d_c)/(7 max(1,h_p/d_p)) = 0.1737
```
So the true constant in (D) appears to be about `1/2`. The proof gives `1/6`.

**Why Theorem CP needed `m >= 8k^2`.** It bounded the invariant subsets that are not pointwise fixed by an additive
count. That count is dominated only while `k^2 = O(m)`, because of the `binom(c, k/2)` unions of whole 2-cycles. Lemma D
does not count invariant subsets. It bounds their probability by the pair-splitting event, which stays a constant
fraction of the event "`X` meets `U` properly" at every `k`.

## Step 2. Tops

Let `g = (g_1, ..., g_l; π) ∈ S_m wr S_l` act by `(A_i)_i -> (g_i A_(π^(-1) i))_i`. Suppose `π ≠ 1`, and pick `i` with
`π^(-1) i = j ≠ i`. A fixed tuple has `A_i = g_i A_j`, so `A_i` is determined by the other coordinates. The fixed
fraction is therefore at most `1/|Δ_k| = 1/binom(m,k) <= 1/m`, since `1 <= k <= m-1`. This is part 1 of CP'.

## Step 3. Ratio transfer

Let `w` have trivial top, `σ(w) = (w_1, ..., w_l; 1)`. It fixes `(A_i)` iff each `w_i` fixes `A_i`, so it moves the
fraction `1 - Π_i (1 - μ_k(w_i))` of `Δ_k^l`. The point model has `h_pt(w) = (1/l) Σ_i b(w_i)`.

**Head.** By the upper half of (D),
```text
h_σ(z) <= min(1, Σ_i μ_k(z_i)) <= min(1, k' Σ_i b(z_i)) = min(1, k' l h_pt(z)).
```

**Defect.** By the lower half of (D), and `Σ_i min(1, y_i) >= min(1, Σ_i y_i)` for `y_i >= 0`,
```text
δ_σ(r) = 1 - Π_i (1 - μ_k(r_i)) >= 1 - exp(-Σ_i μ_k(r_i)) >= 1 - exp(-y),   y = min(1, k' l δ_pt(r))/6 <= 1/6.
```
By concavity, `1 - e^(-y) >= 6(1 - e^(-1/6)) y >= 0.921 y` on `[0, 1/6]`. So
`δ_σ(r) >= 0.1535 min(1, k' l δ_pt(r)) >= (1/7) min(1, k' l δ_pt(r))`.

**Ratio.** Take `r` with `δ_pt(r) = δ_pt`. Then `δ_σ >= δ_σ(r)`, and `min(1,A)/min(1,B) <= max(1, A/B)` for `A, B > 0`. So
```text
h_σ(z)/δ_σ <= 7 min(1, k' l h_pt(z)) / min(1, k' l δ_pt) <= 7 max(1, h_pt(z)/δ_pt).
```
If `δ_pt = 0`, then either `h_pt(z) = 0`, so that `h_σ(z) = 0` as well, or the ratio `h_pt/δ_pt` is `+∞` and the
inequality is empty. This is (CP'). The factor `k' l` cancels, which is the whole point: Theorem CP lost `4k` because its
lower bound on the defect had no factor `k`.

## Step 4. Theorem HD

The direction (b) ⇒ (a) is immediate. For (a) ⇒ (b), suppose (b) fails. Then for every `n` there is a Hamming model
`σ_n` on some `Ω_n` with `h_n := h_(σ_n)(z) > n δ_(σ_n, R_n)`. As `h_n <= 1`, this gives `δ_(σ_n, R_n) < 1/n`.

Put `K = ⌈1/h_n⌉`, and let `τ_n` be the diagonal action on `Ω_n^K`. It moves the fraction `1 - (1 - h_(σ_n)(w))^K` of
tuples. Hence:
- for `r ∈ R_n`, `δ_(τ_n)(r) <= K δ_(σ_n)(r) <= 2 δ_(σ_n)(r)/h_n < 2/n`;
- `h_(τ_n)(z) >= 1 - (1 - h_n)^K >= 1 - e^(-1)`.

For each fixed `j`, `R_j ⊂ R_n` once `n >= j`. So `δ_(τ_n, R_j) -> 0` while the head stays at least `1 - 1/e`,
contradicting (a). ∎

## Step 5. The Jacobson corollary

Let `σ_n` be configuration models of type `(m_n, k_n, l_n)`, with no condition on `k_n`, such that `δ_(n,j) -> 0` for
every window `R_j` and `h_(σ_n)(z) >= c > 0`.

**Tops are trivial.** Fix a window `R_(j_0)` that contains a finite presentation of `St_4(J)`
(`steinberg-finite-presentation-and-kazhdan-theorem`). Once `δ_(n, j_0) < 1 - 1/m_n`, Step 2 shows that every relator in
that window has trivial top. So the tops define a homomorphism `St_4(J) -> S_(l_n)`, and its image is finite. Every
finite image of a group satisfying the Steinberg relations over `J` in indices `1, 2, 3` kills `x_13(Q)`. This is Item 1
of `cohn-elementary-group-is-not-lef`, by the pigeonhole Steinberg chain. So `z` has trivial top, and Step 3 applies to
every window containing `R_(j_0)`.

**Ratio blow-up.** Fix a window `j >= j_0`. Once `δ_(n,j) < 1/7`, the defect bound of Step 3 forces
`k'_n l_n δ_(pt,j) <= 7 δ_(n,j)`. The head bound gives `k'_n l_n h_pt(z) >= c`. Dividing,
```text
h_pt(z) / δ_(pt, j)  >=  c / (7 δ_(n,j))  ->  ∞.
```
Smaller windows only lower `δ_pt`. So the point models `σ_(n,pt)` on `[m_n] x [l_n]` violate (b) of Theorem HD for every
window, and by Step 4 their tuple powers are Hamming models with defect `-> 0` on every window and head at least
`1 - 1/e`.

Conversely, a Hamming model on `[m]`, `m >= 2`, is a configuration model of type `(m, 1, 1)`. So configuration models,
of arbitrary subset sizes and block numbers, see the head iff Hamming point models do. ∎

## Scope

- Only permutation models through `S_m wr S_l` in product action on `Δ_k^l` are treated. Subgroups `G` with
  `A_m^l <= G <= S_m wr S_l` are included, because the statement concerns arbitrary maps into the wreath product.
- The identification of branch (M) sections as this product action is the recalled Liebeck–Saxl / Guralnick–Magaard
  classification. It is still not imported by a `-citation` route, so the claim does not assert that every template
  section is of this form.
- Branch (P), unitary non-permutation models, and the Hamming point problem itself are untouched.
