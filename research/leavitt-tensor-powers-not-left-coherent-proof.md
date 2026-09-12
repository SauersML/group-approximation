---
rg: 2
id: leavitt-tensor-powers-not-left-coherent-proof
kind: route
title: Reduce to the Bernoulli-shift crossed product and show a run-length annihilator is not finitely generated
target: leavitt-tensor-powers-are-not-left-coherent
requires: []
---

Notation: `L = L_k(1,2)` with its `Z`-grading, `L_n` its degree-`n` part,
`x_α = x_(α_1) ⋯ x_(α_m)` and `y_β = y_(β_m) ⋯ y_(β_1)`. Then
`L_0 = span{x_α y_β : |α| = |β|}` and `x_α y_β = Σ_i x_α x_i y_i y_β`.

**Step 1 (reduction to total degree zero).** `A = L ⊗ L` is `Z`-graded by total
degree, `A_m = ⊕_(i+j=m) L_i ⊗ L_j`.
- It is strongly graded: `(x_1⊗1)(y_1⊗1) + (x_2⊗1)(y_2⊗1) = 1` lies in
  `A_1 A_(−1)`, and `(y_1⊗1)(x_1⊗1) = 1` lies in `A_(−1) A_1`.
- Put `T = A_0 = ⊕_n L_n ⊗ L_(−n)`.

*Lemma.* If `A` is left coherent, then `ann_T(f) = {g ∈ T : g f = 0}` is a
finitely generated left ideal of `T` for every `f ∈ T`.

*Proof.* `A f` is finitely generated, hence finitely presented, so `ann_A(f)`
is finitely generated. It is graded, because `f` has degree `0`, and its
degree-zero part is `ann_T(f)`.
- Choose homogeneous generators `a_i` of degrees `d_i`. Then
  `ann_T(f) = Σ_i A_(−d_i) a_i`.
- Each `A_(−d)` is a finitely generated left `T`-module. Write
  `1 = Σ_k p_k q_k` with `p_k ∈ A_d` and `q_k ∈ A_(−d)`. For `c ∈ A_(−d)`,
  `c = Σ_k (c p_k) q_k` with `c p_k ∈ T`.

**Step 2 (T is the Bernoulli crossed product).**
- Let `u = x_1⊗y_1 + x_2⊗y_2` and `v = y_1⊗x_1 + y_2⊗x_2`. Then
  `uv = Σ_(i,j) x_i y_j ⊗ y_i x_j = Σ_i x_i y_i ⊗ 1 = 1`, and
  `vu = Σ_(i,j) y_i x_j ⊗ x_i y_j = 1 ⊗ Σ_i x_i y_i = 1`.
- Grade `T` by first-factor degree, `T_(n) = L_n ⊗ L_(−n)`. The element `u` is a
  unit of degree `1`, so `T_(n) = T_0 u^n` and `T = ⊕_n T_0 u^n`, where
  `T_0 = L_0 ⊗ L_0` and `σ(a) = u a u^(−1)` is an automorphism of `T_0`.
- **Matrix units.** Identify `T_0` with the restricted tensor product
  `⊗'_(p∈Z) M_2(k)`: `x_α y_β ⊗ x_γ y_δ`, with `|α| = |β| = m` and
  `|γ| = |δ| = n`, is the tensor with `e_(α_1 β_1)` at position `0`, ...,
  `e_(α_m β_m)` at position `−(m−1)`, `e_(γ_1 δ_1)` at position `1`, ...,
  `e_(γ_n δ_n)` at position `n`, and `1` elsewhere. The identity
  `x_α y_β = Σ_i x_α x_i y_i y_β` shows that this is well defined.
- **The shift.** For `n >= 1`, `y_i x_γ = δ_(i γ_1) x_(γ')` and
  `y_δ x_j = δ_(δ_1 j) y_(δ')`, with `γ' = γ_2 ⋯ γ_n`. So
  `σ(x_α y_β ⊗ x_γ y_δ) = Σ_(i,j) x_i x_α y_β y_j ⊗ y_i x_γ y_δ x_j = x_(γ_1 α) y_(δ_1 β) ⊗ x_(γ') y_(δ')`.
  The case `n = 0` is the same computation. Hence
  `σ(e^(p)_(ab)) = e^(p−1)_(ab)`: `σ` is the Bernoulli shift.

**Step 3 (the annihilator).** Let `e = x_1 y_1 ⊗ 1 = e^(0)_(11)` and
`f = (1 − u) e`. For `g = Σ_n g_n u^n` with `g_n ∈ T_0`,
`g f = Σ_n (g_n − g_(n−1)) σ^n(e) u^n` and `σ^n(e) = e^(−n)_(11)`. So

```text
(*)   g ∈ ann_T(f)   iff   (g_n − g_(n−1)) e^(−n)_(11) = 0 for every n.
```

**Step 4 (column vectors).** Let `X = {1,2}^Z`.
- For `x ∈ X` let `V_x` have basis `ξ_s` for the `s ∈ X` differing from `x` in
  finitely many coordinates. `T_0` acts coordinatewise, with
  `e^(p)_(ab) ξ_s = [s_p = b] ξ_(s')`, where `s'` is `s` with `s_p` replaced
  by `a`.
- (a) If `h e^(p)_(11) = 0` and `x_p = 1`, then `h ξ_x = h e^(p)_(11) ξ_x = 0`.
- (b) Let `(τ x)_p = x_(p+1)` and `Θ ξ_s = ξ_(τ s)`. Then
  `Θ e^(p)_(ab) Θ^(−1) = e^(p−1)_(ab)`, so
  `σ^j(h) ξ_x = Θ^j (h ξ_(τ^(−j) x))`. In particular `σ^j(h) ξ_x = 0` iff
  `h ξ_(τ^(−j) x) = 0`.

**Step 5 (blocks).** Link `n − 1` and `n` when `x_(−n) = 1`. The maximal linked
intervals of `Z` are finite *blocks* `[a, b]`, with `x_(−a) = 2`,
`x_(−n) = 1` for `a < n <= b`, and `x_(−(b+1)) = 2`, or infinite runs. Let `g`
lie in `ann_T(f)`, with `g_n = 0` outside an interval of width `w`, and put
`G_x(n) = g_n ξ_x`.
- By `(*)` and (a), `G_x(n) = G_x(n−1)` whenever `x_(−n) = 1`.
- So `G_x` is constant on each block and each infinite run. Since it is finitely
  supported, it vanishes on infinite runs and on every block of length `> w`.

**Step 6 (left multiples keep the bound).** For `c ∈ T_0`,
`(c u^j g)_n ξ_x = c Θ^j(g_(n−j) ξ_(τ^(−j) x))` by (b). Since
`(τ^(−j) x)_(−(n−j)) = x_(−n)`, the blocks of `τ^(−j) x` are those of `x`
translated by `−j`.
- If `n` lies in a block of `x` of length `> w`, then `n − j` lies in a block of
  `τ^(−j) x` of the same length, and so `(c u^j g)_n ξ_x = 0`.
- Every element of `T` is a sum of terms `c u^j`. So if `g^(1), ..., g^(r)` in
  `ann_T(f)` all have width `<= W`, every `h` in the left ideal they generate
  satisfies `h_n ξ_x = 0` whenever `n` lies in a block of `x` of length `> W`.

**Step 7 (long annihilators).** For `ℓ >= 1` let
`P_ℓ = e^(0)_(22) e^(−1)_(11) ⋯ e^(−ℓ)_(11) e^(−ℓ−1)_(22)` and
`g^[ℓ] = Σ_(n=0)^(ℓ) P_ℓ u^n`.
- `g^[ℓ]_n − g^[ℓ]_(n−1)` is `P_ℓ` at `n = 0`, is `−P_ℓ` at `n = ℓ+1`, and is
  `0` otherwise. Since `P_ℓ e^(0)_(11) = 0 = P_ℓ e^(−ℓ−1)_(11)`, `(*)` gives
  `g^[ℓ] ∈ ann_T(f)`.
- Take `x` with `x_0 = 2`, `x_(−1) = ⋯ = x_(−ℓ) = 1` and `x_(−ℓ−1) = 2`. Then
  `[0, ℓ]` is a block of `x` of length `ℓ + 1`, and
  `g^[ℓ]_0 ξ_x = P_ℓ ξ_x = ξ_x ≠ 0`.

**Step 8 (conclusion for d = 2).**
- If `ann_T(f)` were generated by finitely many elements of width `<= W`, Step 6
  with `ℓ = W` would give `g^[W]_0 ξ_x = 0` for the `x` of Step 7,
  contradicting Step 7. So `ann_T(f)` is not finitely generated, and by the
  Lemma `A` is not left coherent.
- Explicitly, `A f` is not finitely presented. Since `1 − u` is not a right zero
  divisor (right multiplication by the unit `u` moves `Z^2`-degrees by
  `(1, −1)`), `g ↦ g(1 − u)` identifies `ann_A(f)` with
  `A(1 − u) ∩ A(1 − e)`.
- **Right coherence.** `x_i ↔ y_i` in both factors is an anti-automorphism of
  `A`, so `A^op ≅ A` and `A` is not right coherent either.

**Step 9 (d >= 3).** Let `R = L^(⊗(d−2))` and grade `L^(⊗d) = A ⊗ R` by the total
degree of the first two factors.
- It is strongly graded, with degree-zero ring `T ⊗ R = ⊕_n (T_0 ⊗ R) u^n`, and
  the Lemma holds verbatim.
- Run Steps 3–8 with `h ∈ T_0 ⊗ R` acting on `V_x ⊗_k R`, where `R` acts on
  itself by left multiplication.
  - (a) holds because `e^(p)_(11) ⊗ 1` fixes `ξ_x ⊗ 1`.
  - (b) holds with `Θ ⊗ 1`.
  - Step 7 uses `g^[ℓ] ⊗ 1`, and `(P_ℓ ⊗ 1)(ξ_x ⊗ 1) = ξ_x ⊗ 1 ≠ 0`.
- So `L^(⊗d)` is neither left nor right coherent.

**By-products.** Steps 3–8 alone show that the Bernoulli crossed product
`T = (⊗'_(Z) M_2(k)) ⋊ Z` is not left coherent. The same steps in the
subalgebra `C(X, k) ⋊ Z`, with evaluation at points in place of `ξ_x`, show
that the crossed product of the full two-shift is not coherent. By contrast,
for a minimal subshift the return times to `[x_0 = 2]` are bounded, and this
witness gives nothing.
