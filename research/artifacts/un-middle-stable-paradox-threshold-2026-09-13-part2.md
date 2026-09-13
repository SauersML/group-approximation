# UN middle, part 2: non-IBN rings, rank reduction to m+1, and the shrunken band

Lane `un-middle`, 2026-09-13. Unreviewed. Part 1: `un-middle-stable-paradox-threshold-2026-09-13.md`.

## 1. Theorem 5 (non-IBN rank reduction)
Let `R` be a countable unital ring with `R^m ≅ R^{m+d}` as right modules for some `m ≥ 1` and `d ≥ 1`. Then every
homomorphism from `EL_N(R)` to an MF group is trivial for every `N ≥ max(m+1, 3)`. If `m = 1`, also for `N = 2`
(part 1, Theorem 1).

Such `R` are exactly the rings receiving a unital homomorphism from a Leavitt algebra of module type `L(m, m+d)`.

## 2. Proof
**(1) A high rank with full MF radical.**
- `R^m ≅ R^{m+d} = R^{m+1} ⊕ R^{d−1}` gives `(m+1)[R] ≤ m[R]`.
- So part 1 Theorem 1 (`paradoxical-ring-el-n-full-mf-radical-from-twice-level`) gives full MF radical of `EL_M(R)` for
  every `M ≥ 2m`.
- Composing the isomorphism with itself, `R^m ≅ R^{m+jd}` for every `j ≥ 1`. Fix `j` with `M := N + jd ≥ 2m`.
- Let `X ∈ M_{m×(m+jd)}(R)` and `Y ∈ M_{(m+jd)×m}(R)` with `XY = 1_m` and `YX = 1_{m+jd}`.

**(2) The conjugation.**
- Put `f := N − m ≥ 1` (free coordinates), `A := diag(X, 1_f) ∈ M_{N×M}(R)` and `B := diag(Y, 1_f) ∈ M_{M×N}(R)`.
- Then `AB = 1_N` and `BA = 1_M`.
- So `Φ : GL_M(R) → GL_N(R)`, `g ↦ AgB`, is a group isomorphism: `Φ(g)Φ(h) = Ag(BA)hB`, with inverse `h ↦ BhA`.

**(3) `Φ(EL_M(R)) ⊆ EL_N(R)`.** Let `c = m+jd+1` be a free index of `R^M`, and `c' = m+1` the matching index of `R^N`.
Column `c` of `A` and row `c` of `B` are the unit vectors at `c'`. For `i ≤ m+jd`, column `i` of `A` is
`(x_1i, …, x_mi, 0, …)^T` and row `i` of `B` is `(y_i1, …, y_im, 0, …)`. Hence

```text
Φ(e_{ic}(r)) = 1 + Σ_{k≤m} E_{kc'} x_ki r  = Π_{k≤m} e_{kc'}(x_ki r),
Φ(e_{ci}(r)) = 1 + Σ_{k≤m} E_{c'k} r y_ik  = Π_{k≤m} e_{c'k}(r y_ik),
```

and the factors in each product commute. Free–free elementary matrices map to free–free elementary matrices. For `i ≠ j`
in the X-block, `e_ij(r) = [e_ic(r), e_cj(1)]`, so `Φ(e_ij(r)) ∈ EL_N(R)` too.

**(4) Isolating one transvection.** Let `φ : EL_N(R) → M` be a homomorphism into an MF group.
- By (1)–(3), `φ ∘ Φ` is trivial, so `g_i(r) := Π_{k≤m} e_{kc'}(x_ki r)` lies in `ker φ` for all `i` and `r`.
- *Case `m = 1`.* Here `g_i(r) = e_{1c'}(x_1i r)`, so `e_{1c'}(Σ_i x_1i y_i1) = e_{1c'}(1) ∈ ker φ`.
- *Case `m ≥ 2`.* For `k ≠ k' ≤ m`, `e_{kk'}(s)` commutes with every `e_{lc'}(·)` with `l ≠ k'`, and
  `e_{kk'}(s) e_{k'c'}(b) e_{kk'}(−s) = e_{kc'}(sb) e_{k'c'}(b)`. So
  `e_{kk'}(s) g_i(r) e_{kk'}(−s) · g_i(r)^{-1} = e_{kc'}(s x_{k'i} r) ∈ ker φ`.
  With `s = 1` and `r = y_{ik'}`, multiplying over `i` gives `e_{kc'}(Σ_i x_{k'i} y_{ik'}) = e_{kc'}(1) ∈ ker φ`, since
  `XY = 1_m`.
- *Normal generation (`N ≥ 3`).* `[e_{ak}(r), e_{kc'}(1)] = e_{ac'}(r)` for `a ∉ {k, c'}`. Signed permutations
  `e_kl(1) e_lk(−1) e_kl(1)` then give every `e_ij(±r)`, so `φ` is trivial. ∎

## 3. Consequences and calibration
- **`L_k(1,n)`:** the full MF radical in every rank `N ≥ 2` is recovered, from part 1 and Theorem 5.
- **Module type `L_k(m, m+d)` with `m ≥ 2`:** full MF radical for every `N ≥ m+1`. For `m = 2`, this is every
  `N ≥ 3`.
  - So `EL_N(L_k(2,3))` is a finitely generated Kazhdan group with no nontrivial MF quotient for every `N ≥ 3`
    (`elementary-groups-over-fg-rings-have-property-t`).
  - Recalled, not verified here: Cohn (Topology 5, 1966) proved `L(m,n)` with `m ≥ 2` is an `(m−1)`-fir, hence a domain
    and directly finite.
  - If so, these are Kazhdan elementary groups with no MF quotient over a *directly finite* ring, outside the reach of
    `cor:simple-infinite-ring`.
- **Part 1's candidate dies.** The candidate `EL_3(L_k(2,3))` for the band has full MF radical.

## 4. The band after Theorem 5
- **Rings of module type `(m, m+d)`, `m ≥ 3`:** the band is `3 ≤ N ≤ m`.
  - At `N ≤ m` there is no free coordinate. Recalled (Bergman): `R^i ≅ R^j` only if `i = j` or `i, j ≥ m`, so no exact
    IBN failure below rank `m`.
  - `Φ(e_ij(r)) = 1 + x_i r y_j` with `y_j x_i = 0` is not visibly elementary.
  - Simplest open case: `EL_3(L_k(3,4))`.
- **Paradoxical rings with no exact IBN failure** (only `R^n ≅ R^{n+1} ⊕ Q` with `Q` not stably free): part 1's band
  `3 ≤ N < 2p` stands. The conjugation trick needs an exact isomorphism with a free coordinate.
