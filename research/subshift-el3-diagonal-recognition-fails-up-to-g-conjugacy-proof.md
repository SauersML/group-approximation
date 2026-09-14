---
rg: 2
id: subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy-proof
kind: route
title: Half-orbit Fredholm index, standard diagonals are scalar twists of the diagonal, and diag(u,1,1) has index −1
target: subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy
requires: []
artifacts:
  - research/artifacts/sk-diagonal-recognition-2026-09-13-part1.md
---

Notation as in the target. Fix `x ∈ X`, let `V = ⊕_{t∈Z} F_2^3 δ_t` with `fδ_t = f(T^tx)δ_t` and `uδ_t = δ_{t+1}`
(this is a representation of `M_3(R)`, since `ufu^{-1}δ_t = f(T^{t−1}x)δ_t = (f∘T^{-1})δ_t`), and let `P` project onto
`t ≥ 0`.

**Step 1 (index).**
- Let `w_0` bound the powers of `u` in the entries of `g` and `g^{-1}`. Then `(1−P)gP` and `Pg(1−P)` are supported on
  `|t| ≤ w_0`, so they have finite rank.
- `(PgP)(Pg^{-1}P) = P − Pg(1−P)g^{-1}P`, and symmetrically, so `PgP` is Fredholm.
- `PghP − (PgP)(PhP) = Pg(1−P)hP` has finite rank, so `ind` is additive.
- Over `F_2`, `e_ij(r)^2 = I`, so `2·ind(e_ij(r)) = 0` and `ind` vanishes on `E_3(R)`.
- `wI_3` is block diagonal over three copies of `⊕_t F_2δ_t`, so `ind(wI_3) = 3·ind_1(w)`.
- `u` compresses to the unilateral shift, so `ind(d) = ind_1(u) = −1`.

**Step 2 (item 2).**
- `B` is Boolean: every element is a sum of idempotents, and in characteristic 2 a sum of commuting idempotents is
  idempotent. So `B ≅ LC(Ω,F_2)` and `M_3(B) = LC(Ω, M_3(F_2))`.
- `f_ij := kE_ijk^{-1} ∈ M_3(B)` is a complete system of matrix units. Pointwise at `ω`, choose `v ≠ 0` in the image of
  `f_11(ω)` and let `c(ω)` have columns `f_11(ω)v, f_21(ω)v, f_31(ω)v`. Then `c(ω)` is invertible and
  `f_ij(ω) = c(ω)E_ijc(ω)^{-1}`. The choice is locally constant, so `c ∈ GL_3(B)`.
- `c^{-1}k` commutes with all `E_ij`, so it is `wI_3` with `w ∈ R^×`.
- Centres: `B·I = kZ(M_3(A))k^{-1} = c(wAw^{-1}·I)c^{-1}`, and `c ∈ M_3(B)` fixes `B·I`, so `B = wAw^{-1}`.
- `c` is a product of `e_pq(e_W)` with `W` clopen, since `GL_3(F_2) = E_3(F_2)` and `y ↦ ey + (1−e)I` is
  multiplicative for idempotents `e ∈ B` and sends `e_pq(1)` to `e_pq(e)`. So `ind(c) = 0` and
  `ind(k) = 3·ind_1(w)`.

**Step 3 (item 3).**
- `d e_1j(r)d^{-1} = e_1j(ur)` and `d e_i1(r) d^{-1} = e_i1(ru^{-1})` for `i,j ∈ {2,3}`, while `e_23`, `e_32` are fixed. So
  `dGd^{-1} = G`.
- If `inn(d) = inn(g)` on `G` with `g ∈ G`, then `g^{-1}d` centralizes every root subgroup. By Lemma 1.1 of
  `el3-root-subgroups-are-bicommutant-closed` (entrywise, using `Z(R) = F_2`), it is the identity.
- So `d ∈ G`, contradicting `ind(d) = −1`.

**Step 4 (item 4).**
- Suppose `dLd^{-1} = hGL_3(B)h^{-1}` with `h ∈ G`, and put `k = h^{-1}d`.
- `span_{F_2} L = M_3(A)` and `span_{F_2}GL_3(B) = M_3(B)`: the span of `GL_3(F_2)` is `M_3(F_2)`, applied on each clopen
  piece.
- So `kM_3(A)k^{-1} = M_3(B)`, and Step 2 gives `ind(k) ∈ 3Z`.
- But `ind(k) = ind(h^{-1}) + ind(d) = −1`. Contradiction.

**Step 5 (item 5).**
- If `kLk^{-1} = g k′Lk′^{-1}g^{-1}` with `g ∈ G`, then `n = k′^{-1}g^{-1}k` normalizes `L` and so `M_3(A)`.
- Step 2 with `B = A` gives `ind(n) = ind(k) − ind(k′) ∈ 3Z`.
- `ind(I), ind(d), ind(d^2) = 0, −1, −2`.
- The last assertion is Step 4 with `d` replaced by `k`.

**Model tests.**
- `k = uI_3` has index `−3 ≡ 0`, and `uLu^{-1} = L`. Consistent.
- Only additivity of the index is used, with no `K_1`-stability input.
- The conclusion of `diagonal-recognition-makes-subshift-el3-isos-standard` still holds for `inn(d)`; only its
  `G_Y`-conjugacy hypothesis fails.
