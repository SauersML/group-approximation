---
rg: 2
id: thompson-f-ramsey-radii-in-the-elementary-degree-order-proof
kind: route
title: One Reiter measure balances every test function at once; padding, the sandwich and Towsner's composition place ψ and ψ_l between R and CR; the split is order bookkeeping
target: thompson-f-ramsey-radii-in-the-elementary-degree-order
requires:
  - thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap
  - ramsey-functions-are-pairwise-reiter-radii
  - moore-ramsey-criterion-for-amenability
---

Notation is as in the claim. "Sandwich (a), (b), (c)" and "Corollary 3" refer to
`thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`. The definitions of `R`, `R̃(m, ε, l)` and `F(m, ε)`,
Towsner's inequality `R̃(m, ε, l) ≤ R̃(R̃(m, ε, l−1), ε)` and the monotonicity facts are quoted verbatim in
`moore-ramsey-criterion-for-amenability`. For a measure `ν` and `f : B_n → [0,1]`, `gν(f) = Σ_y (gν)(y) f(y)`.

## Preliminary facts

- **(P1) Monotonicity.** The property "`n` satisfies the defining condition of `R̃(m, ε, l)`" is upward closed in `n`.
  Given functions on `B_{n+1}`, restrict them to `B_n` and keep the witness `ν`, since `P(B_m)ν ⊆ P(B_n) ⊆ P(B_{n+1})`
  and `gν(f)` only reads `f` on `B_n`. The property gets harder as `m` grows (fewer pairs `g, g'`), as `ε` shrinks, and
  as `l` grows. For the last point, let `l' ≤ l` and take `l'` functions. Pad them to `l` functions by repeating the
  last one. A witness for the padded list is a witness for the original list. So
  `R̃(m, ε, l)` is nondecreasing in `m`, in `1/ε` and in `l`. In particular `ψ` and every `ψ_l` are nondecreasing, and
  `R̃(m, 1/u, l) ≤ ψ_l(max(m, u))`.
- **(P2) Window lower bounds.** `F` is infinite and `B_t ⊊ B_{t+1}` for every `t`, since a geodesic word of length
  `t+1` exists. If `ν ≠ 0` and `B_t x ⊆ B_n` for some `x`, then `|B_t| ≤ |B_n|`, so `n ≥ t`. Hence
  `R̃(t, ε, l) ≥ t`, and in particular `ψ_l(t) ≥ t`. Also `R(N) ≥ N` (quoted fact).
- **(P3) `CR(M) ≥ M/2`.** Let `ν ∈ P(B_r)` have `‖gν − ν‖₁ ≤ 1` for all `g ∈ B_M`. If `g·supp ν` and `supp ν` were
  disjoint, the norm would be 2. So `g ∈ supp ν · (supp ν)⁻¹ ⊆ B_{2r}` for all `g ∈ B_M`. Since `B_M` contains an
  element of length `M`, `M ≤ 2r`.
- **(P4) Tower arithmetic.** `exp_0(x) = x` and `exp_{E+1}(x) = 2^{exp_E(x)}`, so `exp_E ∘ exp_{E'} = exp_{E+E'}`, every
  `exp_E` is nondecreasing, and `x ≤ exp_E(x)`. Also `2x ≤ 2^x` for integers `x ≥ 1`, `3y ≤ 2^y` for `y ≥ 4`, and
  `4M ≤ exp_2(M)` for `M ≥ 1`.
- **(P5) `≼` is a preorder.** Reflexivity holds with `E = 0`. For transitivity, suppose `φ ≤ exp_E ∘ χ ∘ exp_E` and
  `χ ≤ exp_{E'} ∘ ω ∘ exp_{E'}`. By monotonicity of `exp_E`,
  `φ(x) ≤ exp_E(exp_{E'}(ω(exp_{E'}(exp_E(x))))) = exp_{E+E'}(ω(exp_{E+E'}(x)))`.

## Clause 1 (l-collapse)

If `F(m, ε) = ∞` there is nothing to prove. Otherwise let `n = F(m, ε)` and take the witness `ν ∈ P(B_n)` with
`P(B_m)ν ⊆ P(B_n)` and `Σ_{g∈B_m} ‖gν − ν‖₁ < ε`. Let `f_0, …, f_{l−1} : B_n → [0,1]` be arbitrary and let
`g, g' ∈ B_m`. If `g = g'` the difference below is `0`. Otherwise, `gν` and `g'ν` are probability measures on `B_n`,
and the balancing fact in `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap-proof` gives
`|gν(f_i) − g'ν(f_i)| ≤ ‖gν − g'ν‖₁/2`. By the triangle inequality this is at most
`(‖gν − ν‖₁ + ‖g'ν − ν‖₁)/2`, which is less than `ε/2`, since `g ≠ g'` are two distinct terms of the sum. The same
`ν` serves for all `i` and every choice of functions, so `n` satisfies the definition of `R̃(m, ε, l)`. ∎

## Clause 2 (two test functions are coarse Reiter)

Fix `M ≥ 1` and `l ≥ 2`, and put `ε = 1/(4M)`.
- `CR(M) ≤ R̃(1, ε, 2)` is sandwich (c), first two inequalities.
- `R̃(1, ε, 2) ≤ R̃(1, ε, l)` is (P1).
- `R̃(1, ε, l) ≤ F(1, ε) ≤ CR(2K) + K + 1` is clause 1 followed by the second inequality of sandwich (b) with
  `m = 1`, `u = 4M`.
- `K_{1,4M} = ⌊200 ln 2 · 25 · 16 M²⌋ + 1 ≤ 55452 M² + 1 ≤ 55453 M²`, since `200 · 400 · ln 2 < 55452`.

For the degree statement, put `t = 4M ≤ exp_2(M)`. By (P1), `R̃(1, ε, l) ≤ R̃(4M, 1/(4M), l) = ψ_l(4M)`. So
`CR(M) ≤ ψ_2(exp_2(M)) ≤ exp_2(ψ_2(exp_2(M)))`, giving `CR ≼ ψ_2`. Likewise `CR ≼ ψ_l`. The reverse bound
`ψ_l ≼ CR` is proved together with `ψ ≼ CR` in clause 3, since that argument uses only clause 1. ∎

## Clause 3 (the chain)

- **`R(t) ≤ ψ(2t)`.** Let `n = R̃(t, 1/2)`, assumed finite, and let `E ⊆ B_n`. Apply the definition with
  `f = 1_E` to get `ν` with `P(B_t)ν ⊆ P(B_n)` and `|gν(E) − g'ν(E)| < 1/2` for all `g, g' ∈ B_t`. For
  `μ, μ' ∈ P(B_t)`, `μν(E) − μ'ν(E) = Σ_{g,g'} μ(g)μ'(g')(gν(E) − g'ν(E))`, so its absolute value is less than `1/2`.
  Hence `B_n` is 1/2-Ramsey with respect to `B_t`, and `R(t) ≤ R̃(t, 1/2)`. By (P1),
  `R̃(t, 1/2) ≤ R̃(2t, 1/(2t)) = ψ(2t)`, since `1/(2t) ≤ 1/2`. As `2t ≤ exp_1(t)`, this gives `R ≼ ψ`.
- **`ψ_l(t) ≤ exp_1(CR(exp_4(t)))` for every `l ≥ 1`.** By clause 1 and sandwich (b) with `m = u = t`,
  `ψ_l(t) ≤ F(t, 1/t) ≤ CR(2K) + K + t`, where `K = K_{t,t} ≥ t` and `2K ≤ exp_3(2t)`. By (P4), `2t ≤ 2^t`, so
  `exp_3(2t) ≤ exp_3(2^t) = exp_4(t)`. Put `N = exp_3(2t)` and `y = CR(N)`. If `y = ∞` the bound is trivial.
  Otherwise `CR(2K) ≤ y` by monotonicity, and `K + t ≤ 2K ≤ N ≤ 2y` by (P3). So `ψ_l(t) ≤ 3y`. Since
  `y ≥ N/2 ≥ 2^{15}`, (P4) gives `3y ≤ 2^y`. So `ψ_l(t) ≤ exp_1(CR(exp_3(2t))) ≤ exp_1(CR(exp_4(t)))`. This gives
  `ψ_l ≼ CR` for every `l`, including `l = 1`, and completes clause 2.
- **`CR(M) ≤ ψ(ψ(4M))`.** Put `ε = 1/(4M)`. Sandwich (c) gives `CR(M) ≤ R̃(a, ε)`, where `a = R̃(1, ε)`. By (P1),
  `a ≤ ψ(4M)`. If `a = ∞`, then `ψ(4M) = ∞` and the bound holds under the convention `ψ(∞) = ∞`. Otherwise put
  `b = ψ(4M)`. Then `a ≤ b`, and `4M ≤ b` by (P2). So by (P1),
  `R̃(a, ε) ≤ R̃(b, 1/b) = ψ(b)`. Hence `CR(M) ≤ ψ(ψ(4M)) ≤ ψ(ψ(exp_2(M)))`, and `CR ≼ ψ∘ψ` with `E = 2`.
  (`ψ∘ψ` is nondecreasing, so `≼` applies to it.) ∎

## Clause 4 (dictionary)

AMP(D) is the statement `R̃(m, 1/u) ≤ exp_D(R(exp_D(m+u)) + u)` for all `m, u ≥ 1`, from
`thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`. CRE(E) is `CR(N) ≤ exp_E(R(exp_E(N)))` for all
`N ≥ 1`, and RGAP₁ is its failure for every `E`; both are from the sandwich claim.
- **AMP(D) ⇒ `ψ ≼ R`.** Take `m = u = t`. Then `ψ(t) ≤ exp_D(y + t)` with `y = R(exp_D(2t))`. If `y = ∞` there is
  nothing to prove. Otherwise `y ≥ exp_D(2t) ≥ 2t ≥ 2` and `y ≥ t`, so by (P4)
  `exp_D(y + t) ≤ exp_D(2y) ≤ exp_D(2^y) = exp_{D+1}(y)`. Also `exp_D(2t) ≤ exp_D(2^t) = exp_{D+1}(t)`, and `R` is
  nondecreasing. So `ψ(t) ≤ exp_{D+1}(R(exp_{D+1}(t)))` for all `t ≥ 1`.
- **`ψ ≼ R` ⇒ AMP(E).** Suppose `ψ(x) ≤ exp_E(R(exp_E(x)))` for all `x`. By (P1),
  `R̃(m, 1/u) ≤ ψ(max(m, u)) ≤ exp_E(R(exp_E(m+u))) ≤ exp_E(R(exp_E(m+u)) + u)`.
- **CRE and RGAP₁.** "CRE(E) for some `E`" is, word for word, `CR ≼ R` with that `E`. RGAP₁ is its negation.
- **AMP(D) gives a double composition.** By the first bullet, `ψ(x) ≤ exp_{D+1}(R(exp_{D+1}(x)))`. Put
  `b = ψ(4M)`. By clause 3 and (P4), `b ≤ exp_{D+1}(R(exp_{D+1}(exp_2(M)))) = exp_{D+1}(R(exp_{D+3}(M)))`. Then
  `CR(M) ≤ ψ(b) ≤ exp_{D+1}(R(exp_{D+1}(b))) ≤ exp_{D+1}(R(exp_{2D+2}(R(exp_{D+3}(M)))))`. ∎

## Clause 5 (the split)

- **RGAP₁ ⇔ ¬AMP ∨ SFG.**
  - (⇐) Suppose RGAP₁ fails, so `CR ≼ R`. Clause 3 gives `ψ ≼ CR` and `R ≼ ψ`. By (P5), `ψ ≼ R`, which is AMP by
    clause 4, and `CR ≼ ψ`, which is SFC. So ¬AMP and SFG both fail.
  - (⇒) Suppose AMP and SFC. Then `CR ≼ ψ ≼ R`, so `CR ≼ R` by (P5), and RGAP₁ fails.
- **RGAP₁ ∧ SFC ⇒ ¬AMP.** This is the contrapositive of (⇒), with SFC held fixed.
- **SFG ⇒ RGAP₁** is (⇐) above.
- **SFG ⇒ `F` is amenable.** Fix `E`. SFG gives `M` with `CR(M) > exp_E(ψ(exp_E(M)))`, so `ψ(exp_E(M)) < ∞`. Since
  `exp_E(M) ≥ exp_E(1)` is unbounded in `E` and `ψ` is nondecreasing (P1), `ψ(x) < ∞` for every `x`. By clause 3,
  `R(t) ≤ ψ(2t) < ∞` for every `t`. As in Corollary 3 of the sandwich, Moore's Theorem 1.3 (2)⇒(4) gives that `F`
  is amenable. Alternatively, SFG ⇒ RGAP₁, and Corollary 3 applies.
- **SFC ⇔ `ψ ≈ CR` ⇔ `ψ ≈ ψ_2`.** The first holds because `ψ ≼ CR` always (clause 3). The second holds because
  `ψ_2 ≈ CR` (clause 2), by (P5).
- **When SFC is automatic.**
  - Suppose `F` is not amenable. Then some `t` has `R(t) = ∞` (Theorem 1.3), so `ψ(x) = ∞` for `x ≥ 2t` by clause 3
    and (P1). Choose `E` with `exp_E(1) ≥ 2t`. Then `exp_E(ψ(exp_E(M))) = ∞ ≥ CR(M)` for every `M`, which is SFC.
  - Suppose instead we work in any infinite finitely generated group `G`, with `ψ_G` and `CR_G` defined in the same way.
    If `CR_G ≤ exp_k` for some `k`, then (P2), which uses only that `G` is infinite, gives
    `CR_G(M) ≤ exp_k(M) ≤ exp_k(ψ_G(M))`. So SFC holds with `E = k`. ∎

## Pair language

Clause (B) of `ramsey-functions-are-pairwise-reiter-radii` gives `R̃(m, ε) = PR_{2ε}(m)` and `R(m) ≤ PR_1(m)`. So
`ψ(t) = PR_{2/t}(t)`. `PR_c(m)` is nondecreasing in `m` and in `1/c`, by the same argument as (P1). For `x ≥ 2`,
`2/x ≤ 1`, so `PR_1(x) ≤ ψ(x)`. Hence `R ≼ PR_1 ≼ ψ ≼ CR`, the middle step using `PR_1(t) ≤ PR_1(2t) ≤ ψ(2t)`.

**SFG ⇒ PGAP_1.** Fix `E ≥ 1`. SFG gives `M` with `CR(M) > exp_E(ψ(exp_E(M)))`. Since `exp_E(M) ≥ 2`, this is at
least `exp_E(PR_1(exp_E(M)))`. That is PGAP_1 at `E`, with `N = M`. For `E = 0`, use the witness for `E = 1`: by
monotonicity, `exp_1(PR_1(exp_1(M))) ≥ PR_1(M)`. ∎
