---
rg: 2
id: busemann-null-isometries-have-no-boundary-contraction-proof
kind: route
title: The horospherical product is quasi-invariant under a Busemann-null isometry, so no boundary point is pushed onto a second fixed point
target: busemann-null-isometries-have-no-boundary-contraction
requires: []
artifacts:
  - research/artifacts/thompson-f-qi-h2-busemann-reduction-2026-09-16.md
---

Notation as in the claim. All Gromov products are based at `o`, and we write `(x|y)` for `(x|y)_o`. The
four-point inequality is used only at the base point `o`. Conventions: `∞ − c = ∞`, and "for large
`i, j`" means for all `i, j ≥ N`, for some `N`.

**Step 0: the boundary is well defined, and isometries act on it.**
- Since `d(x,w) − d(x,o) ∈ [−d(o,w), d(o,w)]`, we have `|(x|y)_w − (x|y)_o| ≤ d(o,w)`.
- `(ky_i|ky_j)_o = (y_i|y_j)_{k^{-1}o}`. So an isometry `k` maps sequences converging at infinity to
  such sequences, and it preserves equivalence. Hence it acts on `∂X`, and `k^{-1}` acts as the
  inverse.
- Equivalence is transitive, because `(y_i|v_l) ≥ min{(y_i|w_j), (w_j|v_l)} − δ`.
- Subsequences represent the same point.
- `0 ≤ (x|y) ≤ min{d(x,o), d(y,o)}`.

**Step 1: basic boundary estimates.**
- **(B1)** If `y_i → u` and `w_j → v`, then `liminf_{i,j} (y_i|w_j) ≥ (u|v) − 2δ`.
  - Let `T` be any real number below `(u|v)`, and `R > T`.
  - Choose `y'_k → u` and `w'_l → v` with `(y'_k|w'_l) > T` for all `k, l ≥ N_0`.
  - By equivalence, there is `N_1` with `(y_i|y'_k) ≥ R` and `(w'_l|w_j) ≥ R` for all
    `i, j, k, l ≥ N_1`.
  - For `i, j ≥ N_1`, take `k = l = max{N_0, N_1}`. Applying the four-point inequality twice gives
    `(y_i|w_j) ≥ min{(y_i|y'_k), (y'_k|w'_l), (w'_l|w_j)} − 2δ ≥ T − 2δ`.
- **(B2)** If `u ≠ v`, then `(u|v) < ∞`. Otherwise, by (B1) any representatives `y_i → u` and
  `w_j → v` satisfy `liminf (y_i|w_j) = ∞`, so they are equivalent and `u = v`.
- **(B3)** `(u|v) ≥ min{(u|t), (t|v)} − 3δ` for `u, v, t ∈ ∂X`.
  - Fix `y_i → u`, `s_k → t`, `w_j → v`, and let `ε > 0`.
  - By (B1), for all `i, j, k ≥ N` we have `(y_i|s_k) ≥ min{(u|t), 1/ε} − 2δ − ε`, and the same bound
    for `(s_k|w_j)` with `(t|v)`.
  - Take `k = N`. Then `(y_i|w_j) ≥ min{(y_i|s_N), (s_N|w_j)} − δ` for `i, j ≥ N`.
  - Let `ε → 0`.

**Step 2: spread of limit points.**
- Let `z_i → ξ` and `z'_j → ξ`, and `y ∈ X`. Choose `i_l, j_l → ∞` with `(y|z_{i_l}) → limsup_i (y|z_i)`
  and `(y|z'_{j_l}) → liminf_j (y|z'_j)`.
- We have `(y|z'_{j_l}) ≥ min{(y|z_{i_l}), (z_{i_l}|z'_{j_l})} − δ`. The second entry tends to `∞`, and the
  first is at most `d(y,o)`.
- So `liminf_j (y|z'_j) ≥ limsup_i (y|z_i) − δ`.
- Put `λ_y := liminf_i (y|z_i) ∈ [0, d(y,o)]` for the fixed `(z_i)`. Applying the inequality both
  ways, every limit point of `(y|z'_j)` lies in `[λ_y − δ, λ_y + δ]`, for any `z'_j → ξ`.

**Step 3: Busemann cocycle.**
- Put `b(y) := limsup_i (d(y,z_i) − d(o,z_i))`. The identity `d(y,z) − d(o,z) = d(y,o) − 2(y|z)` gives
  `b(y) = d(y,o) − 2λ_y` and `b(o) = 0`.
- Let `kξ = ξ` and `z'_i := k^{-1}z_i → ξ`. Then
  `b(ky) = limsup_i [d(y,o) − 2(y|z'_i) − d(k^{-1}o,o) + 2(k^{-1}o|z'_i)]`.
- By Step 2, each bracketed Gromov product is eventually within `δ + ε` of `λ_y`, respectively of
  `λ_{k^{-1}o}`.
- So, with `c(k) := −b(k^{-1}o)`:
  `(**) |b(ky) − b(y) − c(k)| ≤ 4δ` for all `y ∈ X` and all isometries `k` fixing `ξ`.

**Step 4: part (i).**
- For `k, l ∈ G`, apply (**) to `(k, lo)`, `(l, o)` and `(kl, o)`, using `b(o) = 0`. This gives
  `|c(kl) − c(k) − c(l)| ≤ 12δ`.
- We have `q(k) = −d(ko,o) + 2 limsup_i (ko|z_i)` and `b(ko) = d(ko,o) − 2λ_{ko}`. By Step 2,
  `0 ≤ q(k) + b(ko) ≤ 2δ`. By (**) at `y = o`, `|b(ko) − c(k)| ≤ 4δ`. So `|q + c| ≤ 6δ` on `G`.
- **Homogenisation.** Let `φ` be a quasimorphism of defect `D` and `g ∈ G`.
  - `s_n := φ(g^n) + D` is subadditive, and by induction `|φ(g^n) − nφ(g)| ≤ (n − 1)D`.
  - By Fekete's lemma, `φ̄(g) := lim_n φ(g^n)/n` exists, is finite, and satisfies `|φ̄ − φ| ≤ D`.
  - Using subsequences, `φ̄(g^n) = nφ̄(g)` for `n ≥ 0`. From `|φ(e) − φ(g^m) − φ(g^{-m})| ≤ D` we get
    `φ̄(g^{-1}) = −φ̄(g)`.
  - The defect of `φ̄` is at most `4D`: `φ̄(gh) − φ̄(g) − φ̄(h)` differs from `φ(gh) − φ(g) − φ(h)` by
    at most `3D`, since `|φ̄ − φ| ≤ D` at each of the three arguments.
- Apply this with `φ = c` and `D = 12δ`. Since `|q + c| ≤ 6δ`, the limit `p(k) = lim q(k^n)/n` exists
  and equals `−c̄(k)`. So `p` is a homogeneous quasimorphism of defect at most `48δ`.
- **The bound `|p − q| ≤ 18δ`.** Since `p = −c̄` and `|c̄ − c| ≤ 12δ`, we get
  `|p(k) − q(k)| ≤ |c(k) − c̄(k)| + |q(k) + c(k)| ≤ 12δ + 6δ` for every `k ∈ G`.

**Step 5: bounded horofunction shift.**
- Let `kξ = ξ` and `p(k) = 0`, and apply Step 4 to `G = ⟨k⟩`. Then `c̄(k^n) = −p(k^n) = 0` for all
  `n ∈ Z`, so `|c(k^n)| ≤ 12δ`.
- By (**) for `k^n`: `|b(k^n y) − b(y)| ≤ 16δ` for all `n ∈ Z` and `y ∈ X`.
- Put `P(y,w) := (b(y) + b(w) − d(y,w))/2 = (y|w) − λ_y − λ_w`. Since `d(k^n y, k^n w) = d(y,w)`, we get
  `|P(k^n y, k^n w) − P(y,w)| ≤ 16δ`.

**Step 6: Claim A.** If `y_i → u ∈ ∂X \ {ξ}`, then `limsup_i λ_{y_i} ≤ (u|ξ) + δ`.
- Let `T := limsup_i λ_{y_i}`, and fix `R > 0` and `ε > 0`.
- Choose `N` with `(y_i|y_{i'}) ≥ R` for all `i, i' ≥ N`. Then choose `i ≥ N` with
  `λ_{y_i} ≥ min{T, R} − ε`, and `m_0` with `(y_i|z_m) ≥ λ_{y_i} − ε` for `m ≥ m_0`.
- For `i' ≥ N` and `m ≥ m_0`:
  `(y_{i'}|z_m) ≥ min{(y_{i'}|y_i), (y_i|z_m)} − δ ≥ min{T, R} − 2ε − δ`.
- By the definition of `(u|ξ)` as a supremum, `(u|ξ) ≥ min{T, R} − 2ε − δ`.
- By (B2), `(u|ξ) < ∞`. Letting `R → ∞` shows `T < ∞`. Then take `R > T` and let `ε → 0`.

**Step 7: part (ii).** Suppose `kξ = ξ`, `ka = a` with `a ≠ ξ`, `p(k) = 0`, `x ∈ ∂X \ {ξ, a}`, and
`(x_n|a) → ∞`, where `x_n := k^n x`.
1. **Choose representatives.** Pick `y_i → x` and `w_j → a`. By definition, and by (B2),
   `liminf_{i,j} (y_i|w_j) ≤ (x|a) < ∞`. So for each `N` there are `i, j ≥ N` with
   `(y_i|w_j) ≤ Q := (x|a) + 1`. Choose such a pair `(i_N, j_N)` for each `N`, and replace `y_N` by
   `y_{i_N}` and `w_N` by `w_{j_N}`.
   - Since `i_N, j_N ≥ N`, every double liminf over the new indices is at least the corresponding
     double liminf over the old ones.
   - So the new sequences still converge at infinity, and they are equivalent to the old ones.
   - Hence we may assume `(y_i|w_i) ≤ Q` for all `i`, with `y_i → x` and `w_i → a` still.
2. **Upper bound.** Since `λ ≥ 0`, `P(y_i, w_i) ≤ Q`. By Step 5, `P(k^n y_i, k^n w_i) ≤ Q + 16δ` for all
   `n` and `i`.
3. **The new endpoints.** Fix `n ≥ 0`. Then `k^n y_i → x_n` and `k^n w_i → a`. Since `k^n` acts
   bijectively on `∂X` and fixes `ξ` and `a`, we have `x_n ∉ {ξ, a}`.
4. **Lower bound.** Along the diagonal, the liminf is at least the double liminf.
   - By (B1), `liminf_i (k^n y_i|k^n w_i) ≥ (x_n|a) − 2δ`.
   - By Claim A, `limsup_i λ_{k^n y_i} ≤ (x_n|ξ) + δ` and `limsup_i λ_{k^n w_i} ≤ (a|ξ) + δ`.
   - Hence `Q + 16δ ≥ liminf_i P(k^n y_i, k^n w_i) ≥ (x_n|a) − (x_n|ξ) − (a|ξ) − 4δ`.
   - All terms are finite by (B2).
5. **Conclusion.**
   - By (B3), `(a|ξ) ≥ min{(a|x_n), (x_n|ξ)} − 3δ`. Since `(a|x_n) → ∞` and `(a|ξ) < ∞`, for large `n`
     the minimum is `(x_n|ξ)`, so `(x_n|ξ) ≤ (a|ξ) + 3δ`.
   - Substituting into step 4 gives `(x_n|a) ≤ Q + 2(a|ξ) + 23δ` for all large `n`, contradicting
     `(x_n|a) → ∞`. ∎
