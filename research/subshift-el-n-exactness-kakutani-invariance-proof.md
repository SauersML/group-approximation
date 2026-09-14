---
rg: 2
id: subshift-el-n-exactness-kakutani-invariance-proof
kind: route
title: Block transvections give EL_n(M_k(S)) = EL_nk(S); tower matrix units give R over the k-tower as M_k(R); a full corner gives R as a corner of M_k over the induced crossed product
target: subshift-el-n-exactness-is-kakutani-invariant
requires: []
artifacts:
  - research/artifacts/sk-exact-banded-2026-09-14-part1.md
---

Notation as in the target. Write `e_ij(r) = I + rE_ij`.

**Step 0 (exactness passes to subgroups).** For `Λ ≤ Γ`, `C*_r(Λ)` is a C*-subalgebra of `C*_r(Γ)`, and exactness of C*-algebras passes to subalgebras.

**Step 1 (a).**
- Index `GL_{nk}(S) = GL_n(M_k(S))` by pairs `(p,a)` with `p ≤ n` and `a ≤ k`.
- A block transvection `I + AE_pq` with `p ≠ q` and `A ∈ M_k(S)` is the product of the `e_{(p,a),(q,b)}(A_ab)`. So `EL_n(M_k(S)) ⊆ EL_{nk}(S)`.
- Conversely, `e_{(p,a),(q,b)}(s)` with `p ≠ q` is the block transvection `I + sE_ab E_pq`.
- If `p = q` then `a ≠ b`. Choose `p′ ≠ p` (as `n ≥ 2`). Then `e_{(p,a),(p,b)}(s) = [e_{(p,a),(p′,a)}(s), e_{(p′,a),(p,b)}(1)]`, a commutator of block transvections.

**Step 2 (b).**
- `T′` is minimal, since `T′^k` restricted to each level is `T`. If `X` is an infinite subshift, coding by (level, symbol) makes `X^{(k)}` an infinite subshift.
- Let `u′` be the unit of `T′` and `e = e_{X×{0}}`. For `0 ≤ d < k`, `u′^d e u′^{-d} = e_{X×{d}}`; these idempotents sum to `1`, and `e u′^d e = 0` for `0 < |d| < k`.
- So `ε_ij = u′^i e u′^{-j}` (`0 ≤ i,j < k`) is a full system of matrix units, and `R_{X^{(k)}} ≅ M_k(eR_{X^{(k)}}e)`.
- `eR_{X^{(k)}}e` is spanned by the `f u′^{kℓ} e`, with `u′^k e = e u′^k`, and `T′^k` acts on level `0` as `T`. So `f ↦ f(·,0)` and `u ↦ u′^k e` give `R_X ≅ eR_{X^{(k)}}e`. Distinct powers are independent, so the map is injective.
- With (a): `EL_3(R_{X^{(k)}}) ≅ EL_3(M_k(R_X)) = EL_{3k}(R_X)`.

**Step 3 (c), the corner.**
- Let `e = e_V`, and `V = ⊔_n V_n` by first return time `n`. These are finitely many, by minimality.
- `w = Σ_n u^n e_{V_n}` satisfies `ww* = Σ_n e_{T^nV_n} = e_V` and `w*w = e_V`, where `w* = Σ_n e_{V_n}u^{-n}` and `T_V` is a bijection of `V`. Also `wfw^{-1} = f∘T_V^{-1}` on `V`.
- So `f ↦ f` and `v ↦ w` define a ring homomorphism `R_{X_V} → eR_Xe`.
  - **Injective.** Restricted to the sites of the orbit of a point of `V`, it is the orbit representation of `R_{X_V}`, which is faithful because that orbit is dense (as in `banded-matrix-groups-subshift-crossed-product-proof`, Step 4).
  - **Onto.** `e f u^d e` is supported where `x ∈ V` and `T^d x ∈ V`, and there `T^d x = T_V^{j(x)} x` for a locally constant `j`. So it lies in the span of the `LC(V) w^j`.
- The same identification appears in groupoid form in `corner-matrix-ring-isos-force-flip-conjugacy-proof`, Step 1.

**Step 4 (c), the embeddings.**
- **`EL_n(eRe) ≤ EL_n(R)`.** `y ↦ (1−e)I_n + y` is an injective homomorphism `GL_n(eRe) → GL_n(R)`. It sends the elementary matrix `eI_n + rE_ij` (`r ∈ eRe`) to `e_ij(r)`.
- **`R` is a corner of `M_k(eRe)`.**
  - By minimality, finitely many `T^{t_i}V` cover `X`. Choose a clopen partition `X = ⊔_{i≤k} W_i` with `W_i ⊆ T^{t_i}V`.
  - Put `c = (e u^{-t_i} e_{W_i})_i` (a column) and `d = (e_{W_j} u^{t_j} e)_j` (a row). Then `dc = Σ_j e_{W_j} e_{T^{t_j}V} e_{W_j} = 1`.
  - `φ(r) = crd` has entries in `eRe`, is multiplicative (`φ(r)φ(s) = cr(dc)sd = φ(rs)`), and is injective (`dφ(r)c = r`). So `R ≅ fM_k(eRe)f` with `f = cd`.
  - `y ↦ (1−f)I_n + y` embeds `GL_n(fM_k(eRe)f)` in `GL_n(M_k(eRe))` and maps elementary matrices to elementary matrices.
  - So `EL_n(R_X) ≤ EL_n(M_k(R_{X_V})) = EL_{nk}(R_{X_V})` by (a).

**Step 5 (d).**
- `y ↦ diag(y,1)` gives `EL_n(R) ≤ EL_{n+1}(R)`. With Step 0, exactness of `EL_{n+1}` implies exactness of `EL_n`.
- **Kakutani equivalence.** If `X_V ≅ Y_W`, then `EL_n(R_X) ≤ EL_{nk}(R_{X_V}) ≅ EL_{nk}(R_{Y_W}) ≤ EL_{nk}(R_Y)`, and symmetrically.
- **The last bullet.** `EL_n(R_X) ≤ EL_{3n}(R_X) ≅ G_{X^{(n)}}` by Step 2, and `X^{(n)}` is an infinite minimal subshift. ∎

**Model tests.**
- `k = 1` gives `X^{(1)} = X`, and `V = X` gives `X_V = X` ✓.
- A finite orbit of length `p` (not minimal-infinite, but the algebra is the same): `R ≅ M_p(F_2[t^{±1}])`, so `EL_n(R) = EL_{np}(F_2[t^{±1}])` is exact, consistent with (b) ✓.
- For Sturmian `X`, induced systems on cylinders are Sturmian with a Gauss-shifted slope, so (d) makes the exactness question constant along the Gauss orbit ✓. No contradiction with anything on main.
