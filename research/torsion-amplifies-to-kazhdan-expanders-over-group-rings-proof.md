---
rg: 2
id: torsion-amplifies-to-kazhdan-expanders-over-group-rings-proof
kind: route
title: Commutator lengths, the EJZ Kazhdan bound for one-generated rings, and Kazhdan-to-Cheeger
target: torsion-amplifies-to-kazhdan-expanders-over-group-rings
requires:
  - ejz-elementary-groups-explicit-kazhdan-constant
  - brin-thompson-torsion-orders-escape-every-recursive-bound
---

Indices `i, j, k` are distinct elements of `{1,2,3}`, and `[x,y] = xyx^-1y^-1`.

1. **Relations.** `e_ij(a) e_ij(b) = e_ij(a+b)` and
   `[e_ik(a), e_kj(b)] = e_ij(ab)` for all `a, b` in any ring. In
   characteristic `2`, `e_ij(a)^-1 = e_ij(-a) = e_ij(a)`, so every elementary
   matrix is an involution and `Σ_G` is symmetric.
2. **Generation (item 1).** Each element of `F_2[G]` is a finite sum of
   elements of `G`, and each element of `G` is a product of elements of `S`. By
   the two relations, every `e_ij(r)` lies in `<Σ_G>`.
3. **Short elementary matrices.** Let `ℓ(m)` be the largest `Σ_G`-length of
   `e_ij(w)` over all `i ≠ j` and words `w` in `S` of length `m >= 1`. Then
   `ℓ(1) = 1`. Split `w = uv` with `|u| = ⌈m/2⌉` and `|v| = ⌊m/2⌋`. Then
   `e_ij(w) = [e_ik(u), e_kj(v)]`, so `ℓ(m) <= 2ℓ(⌈m/2⌉) + 2ℓ(⌊m/2⌋)`. By
   induction `ℓ(m) <= 2m^2 - 1`:
   - for even `m`, `2(2(m/2)^2 - 1) · 2 = 2m^2 - 4`;
   - for odd `m`, `4(((m+1)/2)^2 + ((m-1)/2)^2) - 4 = 2m^2 - 2`.
4. **The finite subgroups.** Let `m >= 1`, and let `g in G` have finite order
   `n` and `|g|_S <= m`; for `g ≠ 1` step 3 applies to a geodesic word. Then `F_2[<g>] ≅ F_2[x]/(x^n - 1)` is a subring of
   `F_2[G]` with `2^n` elements, generated as a ring by `1` and `g`, since
   `g^-1 = g^(n-1)`. Put `Γ_g = EL_3(F_2[<g>]) <= Λ_G` and
   `T_g = { e_ij(1), e_ij(g) }`.
   - `T_g` is symmetric by step 1, `|T_g| <= 12`, and `T_g ⊂ B_(Σ_G)(2m^2)`
     by step 3.
   - `T_g` generates `Γ_g` by the argument of step 2 inside `F_2[<g>]`.
   - `Γ_g` is finite, being inside `GL_3` of a finite ring, and
     `|Γ_g| >= |{ e_12(r) : r in F_2[<g>] }| = 2^n`.
5. **Kazhdan constant.** Apply `ejz-elementary-groups-explicit-kazhdan-constant`
   with `R = F_2[<g>]`, `x_0 = 1`, `x_1 = g`, `d = 1`, `n = 3`. Then `Σ = T_g`
   and `κ(Γ_g, T_g) >= 1/(8(12√2 + 6 + 36√2)) = 1/(8(48√2 + 6)) > 1/592`,
   since `8(48√2 + 6) < 591.1`.
6. **Kazhdan to Cheeger.** Let `A ⊂ Γ_g` with `0 < |A| <= |Γ_g|/2`, and put
   `f = 1_A - |A|/|Γ_g|` in the left regular representation. It is orthogonal
   to the constants, which are the only invariant vectors.
   - `||f||^2 = |A|(1 - |A|/|Γ_g|) >= |A|/2`.
   - For `y in T_g`, `yf - f = 1_(yA) - 1_A`, so `||yf - f||^2 = |yA Δ A| = 2|A \ yA|`.
   - Some `y` has `||yf - f|| >= κ ||f||`, which gives `2|A \ yA| >= κ^2 |A|/2`.
   - Hence `Σ_(y in T_g) |A \ yA| >= (κ^2/4) |A|`, and `h(Γ_g, T_g) >= κ^2/4 > δ_0`.
7. **Item 2.** For `m >= 1`, choose `g in B_S(m)` of finite order `TO_(G,S)(m)`.
   Steps 4 to 6 make `(Γ_g, T_g)` admissible for
   `X^(δ_0)_(Λ_G)(max(12, 2m^2))`, with `|Γ_g| >= 2^(TO_(G,S)(m))`. This
   includes `g = 1`: then `e_ij(g) = e_ij(1)` has length `1`,
   `F_2[<g>] = F_2`, and `Γ_1 = EL_3(F_2)` has order `168 >= 2`.
8. **Item 3.** If `X^(δ_0)_(Λ_(2V)) <= U` with `U` recursive, then
   `TO_(2V)(m) <= log_2 U(max(12, 2m^2))` for all `m >= 1`, a recursive bound,
   contradicting `brin-thompson-torsion-orders-escape-every-recursive-bound`.
   Passing from "not recursively bounded" to "infinitely often above each
   recursive `U`" is step 3 of that node's proof. ∎
