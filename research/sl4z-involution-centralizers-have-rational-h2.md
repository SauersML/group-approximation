---
rg: 2
id: sl4z-involution-centralizers-have-rational-h2
kind: claim
title: The block-swap involution of SL_4(Z) has centralizer with H^2 = Q, detected by a torus of commuting infinite-order elements
distinct_from:
  sl4z-matricially-stable: that is the stability question; this is a cohomology computation for one torsion centralizer of SL_4(Z), which feeds the delocalized form of Dadarlat's obstruction but decides nothing by itself.
  dadarlat-matricial-stability-obstruction: that sees H^{2k}(SL_4(Z);Q), which vanishes for k >= 1 (recalled, Lee--Szczarba); this is the even cohomology of a centralizer of torsion, where the class lives.
---

**ESTABLISHED** by `sl4z-involution-centralizers-rational-h2-proof` (lane proof,
elementary, not reviewed; no priority claimed).

## Statement

Let `g = [[0, I], [I, 0]] ∈ SL_4(Z)`, in 2x2 blocks (`det g = +1`), and `c = −I_4`.
1. **Centralizer.** `Z_{SL_4(Z)}(g) = { [[A, B], [B, A]] } ≅ Δ`, where
   `Δ = { (X, Y) ∈ GL_2(Z)^2 : X ≡ Y mod 2, det X = det Y }`, via
   `X = A + B`, `Y = A − B`. In these coordinates `g = (I, −I)` and `c = (−I, −I)`.
   Both are central in `Δ`.
2. **Cohomology.** `H^2(Δ; Q) ≅ Q` and `H^1(Δ; Q) = 0`.
3. **Detecting torus.** Put `x = [[1, 2], [0, 1]]` and
   - `M_1 = (x, 1)`, which is `[[A, B], [B, A]]` with `A = [[1,1],[0,1]]`, `B = [[0,1],[0,0]]`;
   - `M_2 = (1, x)`, which is `[[A, −B], [−B, A]]`.

   `M_1, M_2` commute and have infinite order. The restriction
   `H^2(Δ; Q) → H^2(⟨M_1, M_2⟩; Q) = Q` is an isomorphism.
4. **Weyl swap.** `h = diag(1, 1, −1, −1) ∈ SL_4(Z)` satisfies `h g h^{-1} = −g = cg`,
   `h M_1 h^{-1} = M_2` and `h M_2 h^{-1} = M_1`. So `g` and `cg` are conjugate in
   `SL_4(Z)`.
5. **Second involution.** `g_1 = diag(1, −1) ⊕ [[0,1],[1,0]]` also has
   `H^2(Z_{SL_4(Z)}(g_1); Q) ≅ Q`. It is detected by `(T', 1)` and `(1, T')` with
   `T' = [[1, 0], [1, 1]]`, in the eigen-bases `(e_1, e_3 + e_4)` and
   `(e_2, e_3 − e_4)`. The matrix `k : e_1 ↔ e_2, e_3 ↦ e_3, e_4 ↦ −e_4` has
   `det k = 1`, `k g_1 k^{-1} = −g_1`, and it swaps the two coordinates.

## Consequences

- **Dadarlat's obstruction is not absent for `SL_4(Z)`.** It is only moved off the
  identity sector. With route `sl4z-instability-from-delocalized-dadarlat`, the open
  claim `weak-matricial-stability-kills-centralizer-even-cohomology` would refute
  `sl4z-matricially-stable`.
- **Where the class is not.** In `PSL_4(Z)` the image of `h` centralizes the image
  of `g`, and it acts on `H^2(Δ; Q)` by `−1` (proof, step 6). So
  `H^2(C_{PSL_4(Z)}(ḡ); Q) = 0`. The class lives only in `SL_4(Z)`, and only in the
  part where `−I` acts by `−1` (`sl4z-delocalized-bott-lives-in-odd-central-sector`).

## Not claimed

- **No census of all torsion classes.** Other torsion classes were checked for even
  rational cohomology in their centralizers. For `diag(1,1,−1,−1)` and elements of
  orders 5, 8 and 12 (rank-one unit groups), none was found, but this is recalled,
  not proved. The Bianchi-type centralizers `GL_2(Z[i])` and `GL_2(Z[ω])` were not
  settled.
- **No statement about `H^4`** or higher.
