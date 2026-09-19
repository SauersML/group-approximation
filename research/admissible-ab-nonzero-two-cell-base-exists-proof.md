---
rg: 2
id: admissible-ab-nonzero-two-cell-base-exists-proof
kind: route
title: Proof that the cylinder row c of the core (C2) is unimodular over ZG, by reducing ZG/cZG to a free group ring quotient ZF/J, solving 1 in J on a radius-3 ball, and pulling the solution back to an explicit certificate checked in the normal form of F_4 x| Z
target: admissible-ab-nonzero-two-cell-base-exists
requires:
  - rank-five-degree-one-two-cell-configuration-is-a-core
  - two-cell-core-deletions-need-a-unit-fox-coefficient
  - relative-realization-is-relative-efficiency
  - relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two
artifacts:
  - experiments/c2-free-by-cyclic-2026-09-18/verify_unimodular.py
  - experiments/c2-free-by-cyclic-2026-09-18/zg.py
  - experiments/c2-free-by-cyclic-2026-09-18/redJ.py
  - experiments/c2-free-by-cyclic-2026-09-18/searchJ.py
  - experiments/c2-free-by-cyclic-2026-09-18/solveQ.py
  - experiments/c2-free-by-cyclic-2026-09-18/certuni.py
  - experiments/c2-free-by-cyclic-2026-09-18/gamma2.py
  - experiments/c2-free-by-cyclic-2026-09-18/a5check.py
  - experiments/c2-free-by-cyclic-2026-09-18/solvcheck.py
  - experiments/c2-free-by-cyclic-2026-09-18/RESULTS.md
---

Notation is that of the target. `H = π_1(C)` embeds in `G` by
`rank-five-degree-one-two-cell-configuration-is-a-core`, so (C2) is a two-cell core and the
setting of `two-cell-core-deletions-need-a-unit-fox-coefficient` applies, with `ε = 1` and
`g = Xy ∉ H`.

## 1. Exact arithmetic in ZG

By item 1 of the core claim, `G = F_4 ⋊_φ ⟨y⟩`, where `F_4 = ⟨p,q,r,s⟩`, `x_j = y^j x y^{-j}`,
`(p,q,r,s) = (x_{-2},x_{-1},x_0,x_1)` and `φ(x_j) = x_{j+1}`. Every element of `G` has a unique
normal form `u y^m`, with `u` a reduced word in `p,q,r,s` and `m ∈ Z`. `verify_unimodular.py`
computes it directly:
- it rewrites a word in `x, y` as a product of `x_j^{±1}`;
- it expresses `x_2` and `x_{-3}` in the basis by solving `w = 1` for its unique top and bottom
  level letters, and recurses for the other levels;
- it freely reduces.

So an element of `ZG` is a finite map from normal forms to `Z`, and an identity in `ZG` is a
finite check. The script also re-checks the setting: `φ(u_0) = w` and `φ(u_1) = g w g⁻¹` in
`F(x,y)`.

## 2. The certificate (A1)

By (U1), `c_z = g ∂_z u_0 − ∂_z u_1`, with `∂_z` the left Fox derivative, mapped to `G` through
`a ↦ XyxYx`, and so on. `verify_unimodular.py` forms each `c_z` and each `d_z` of (A1) in normal
form, multiplies them in `ZG`, and gets `Σ_z c_z d_z = 1` exactly (output in `RESULTS.md`). This
proves (A1). The certificate is independent of how it was found. Section 4 records the search
only so it can be reproduced.

## 3. Consequences (A2)–(A4)

- **(A2).** By (U2), `pd_{ZG} I_{G/H} ≤ 1`. The map `ZG^5 → ZG`, `v ↦ Σ c_z v_z`, is split by
  `1 ↦ d`. Its kernel `K` satisfies `K ⊕ ZG ≅ ZG^5`, so `K` is stably free of rank 4.
- **(A3).** By the core claim, `H` is a degree-one `(1,2)` base, so `ab = 2 ≠ 0`. By (U4) no
  `c_y` is a unit in any free basis, and by (U3) no one-cell deletion presents `G`.
- **(A4).** `n(C) = 2`, so Theorem 3 of `relative-realization-is-relative-efficiency` gives
  `ρ(H,G) ≤ 1`, and Theorem 2 gives `ρ(H,G) = 0 ⟺ RP(H,G)`. The group `G` is one-relator,
  torsion-free and not free, so `cd G = 2`. `H` is countable and `C` is a 2-dimensional
  `K(H,1)`. With (A2), the last sentence of `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two`
  gives `cd Γ_κ(H,G) ≤ 2`, and its (a) ⟺ (c) gives `RP(H,G) ⟺ gd Γ_{ℵ_1}(H,G) ≤ 2`.
  - If `ρ(H,G) = 1`, then `gd Γ_{ℵ_1} ≥ 3`. The Eilenberg–Ganea theorem gives
    `gd ≤ max(3, cd) = 3`, so `cd = 2` and `gd = 3`.
  - If `ρ(H,G) = 0`, then RP holds. The relative presentation count
    `|R| − |T| = 2 − |S| − χ(H) = 2 − 2 + 2 = 2` is the one in Theorem 2.

## 4. How the certificate was found (discovery, not needed for the proof)

Write elements in right-coefficient form `Σ y^m f_m` with `f_m ∈ ZF`, using `f y = y φ⁻¹(f)`.
- `c_a = α_0 + y α_1` with `α_1 = −p` a unit. So modulo the right ideal `I = c·ZG`,
  `y ≡ τ := −α_0 α_1⁻¹ = rSq + rSqPRSrp`.
- `c_e` gives `y⁻¹ ≡ τ Q s φ(·)` in the same way.

Hence `ZG / I` is generated over `ZF` by the class of 1, and it equals `ZF / J`. Here `J` is the
smallest right ideal of `ZF` stable under `T(h) = τ φ⁻¹(h)` and `T⁻¹` that contains the
reductions of `c_b, c_c, c_d` and of `T T⁻¹(1) − 1` (`redJ.py`). Modulo `J`,
`T² ≡ Rp φ⁻²(·)`.

`searchJ.py` tests `1 ∈ J` on generators `M^k(γ)` and `M^k(Tγ)` (`|k| ≤ K`), multiplied by the
radius-`R` ball of `F_4`. Radius 2 fails. Radius 3 with `K = 0` succeeds mod 1009. `solveQ.py`
solves that system exactly over `Q` and finds 9 terms with coefficients `±1`. `certuni.py`
carries every generator together with its expression `Σ_z c_z E_z` through `T`, and through the
substitutions for `y` and `y⁻¹`. It then assembles `d` and re-verifies `Σ c_z d_z = 1`.

## 5. The slide route (A5)

`Y_1 = ⟨B, x, y | u_0, u_1, r_z (z ∈ B)⟩` has `π_2(Y_1) = ZG σ`, with
`σ = ẽ_1 − g ẽ_0 + Σ_z c_z r̃_z` (U1). For `z ≠ c`, replace `r_z` by
`r_z' = r_z · Π_i (w_i r_c^{n_i} w_i⁻¹)`, where `d_z = Σ_i n_i w_i`. This is a sequence of
relator slides, so it does not change `π_1` or the homotopy type, and it contains `K_B`.

In the new basis of 2-cells, the `r_c`-coefficient of `σ` becomes
`c_c − Σ_{z≠c} c_z d_z = −(Σ_z c_z d_z) = −1`, using `d_c = −1`.

Let `Y''` be the result with `r_c` deleted, and `N = ker(π_1 Y'' → G)`.
- **N is perfect.** Let `Ŷ` be the `N`-cover of `Y''`. Adding the `G`-orbit of lifts of `r_c`
  gives the universal cover `Ỹ_1'`. In the exact sequence
  `H_2(Ỹ_1') → H_2(Ỹ_1', Ŷ) ≅ ZG → H_1(Ŷ) → H_1(Ỹ_1') = 0`, the first map sends `σ` to its
  `r_c`-coefficient `−1`, so it is onto. Hence `N^{ab} = H_1(Ŷ) = 0`.
- **If N = 1,** then `χ(Y'') = χ(Y_1) − 1` gives `ρ(Y'') = 0`. So `Y''` is aspherical by
  Theorem 1 of `relative-realization-is-relative-efficiency`, contains `K_B ≃ C`, and realizes
  `RP(H,G)`.

Eliminating `a, b, d, e` through their slid relators `r_z'` and writing `c = t φ(c)` presents
`π_1(Y'')` as `⟨t, x, y | R_0, R_1⟩`, where `R_j` is `u_j` after the substitution
(`gamma2.py`). Putting `t = 1` recovers `⟨x, y | w, g w g⁻¹⟩ = G`, so `N = ⟨⟨t⟩⟩`. As a
consistency check, GAP gives `Γ''^{ab} = Z² = G^{ab}`.

**(A6).** `a5check.py` runs over `x` up to conjugacy in `A_5` and over all `y`, and all
`t ≠ 1`. It evaluates `R_0` and `R_1` with a multiplication table and finds 18 solutions, for
example (as image lists) `t = (3,1,0,2,4)`, which is the 3-cycle `(0 3 2)`, `x = (0,2,1,4,3)`
and `y = (1,3,0,4,2)`. So `t ≠ 1` in `Γ''`. GAP's `GQuotients(Γ'', A_5)` independently finds 2
epimorphisms up to automorphism, both with `t ≠ 1`. It also finds 5 onto `S_5` and 2 onto
`PSL(2,7)`, all with `t ≠ 1`, and none onto `S_4` or `A_6`. Hence `N ≠ 1` and this `Y''` is
not a relative presentation of `G`. That is consistent with `N` being perfect, since `t`
normally generates `A_5`.

As a check on the construction, `solvcheck.py` finds that every homomorphism of `Γ''` to
`S_4`, `D_5`, `D_6`, `Z_3 ≀ Z_2` or `AGL(1,5)` kills `t`. That is what perfectness of `N`
predicts.
