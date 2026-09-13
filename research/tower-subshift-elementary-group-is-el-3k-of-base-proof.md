---
rg: 2
id: tower-subshift-elementary-group-is-el-3k-of-base-proof
kind: route
title: Level idempotents and powers of u form k-by-k matrix units whose corner is the base crossed product, and in-block transvections are commutators
target: tower-subshift-elementary-group-is-el-3k-of-base
requires: []
---

Notation as in the claim. Write `e_V` for the indicator of a clopen set `V`, and `u` for the implementing unit,
with `u f u^(-1) = f∘S^(-1)`, so `u e_V u^(-1) = e_(SV)`.

**1. Subshift.**
- `X^(k)` is a Cantor space and `S` is a homeomorphism.
- `S^k` preserves `X×{0}` and acts there as `T`, so every `S`-orbit meets `X×{0}` in a `T`-orbit. `T` is
  minimal and `S` permutes the levels cyclically, so `S` is minimal. `X^(k)` is infinite.
- Code `(x,i)` by the letter `(x_0, i) ∈ A × {0,…,k−1}`. The coding of `S^n(x,i)` is
  `(x_(⌊(i+n)/k⌋), (i+n) mod k)`. So the itinerary map is continuous, injective and equivariant, and
  `(X^(k),S)` is conjugate to its image, a minimal subshift.

**2. Matrix units.**
- Put `p_i = e_(X×{i})` for `0 ≤ i ≤ k−1`. These are orthogonal idempotents with `Σ p_i = 1`.
- For `0 ≤ i,j ≤ k−1`, `S^(i−j)` maps level `j` onto level `i` with no wrap-around. So
  `u^(i−j) p_j u^(j−i) = p_i`, and `v_ij := p_i u^(i−j) = u^(i−j) p_j`.
- Then `v_ij v_jl = p_i u^(i−j) u^(j−l) p_l = v_il`, and `v_ij v_(j'l) = u^(i−j) p_j p_(j') u^(j'−l) = 0` for
  `j ≠ j'`. Also `Σ_i v_ii = 1`.
- A unital ring with a complete system of `k × k` matrix units is `M_k` of the corner at `v_00`. So
  `R_(X^(k)) ≅ M_k(p_0 R_(X^(k)) p_0)`.

**3. The corner.**
- `p_0 f u^n p_0 = f p_0 p_(S^n-level) u^n` vanishes unless `k | n`, since `S^n` maps level 0 to level `n mod k`.
  So `p_0 R p_0` is spanned by the elements `(f p_0) u^(km) p_0`.
- `w = u^k p_0` is a unit of the corner, with inverse `u^(−k) p_0`. Conjugation by `w` acts on `LC(X×{0}) ≅ LC(X)` as `T`.
- The map `R_X → p_0 R p_0` sending `f ↦ f⊗p_0` and `u ↦ w` preserves the defining relation, so it is a ring
  homomorphism. It is onto by the spanning set.
- It is injective: `Σ_m f_m u^m ↦ Σ_m (f_m⊗p_0) u^(km)`, and distinct powers of `u` are independent over
  `LC(X^(k))` in the crossed product.
- So `R_(X^(k)) ≅ M_k(R_X)`.

**4. `EL_n(M_k(R)) = EL_(nk)(R)`, `n ≥ 2`.** Index `R^(nk)` by pairs `(p,a)`.
- **(⊆)** For `i ≠ j` and `A ∈ M_k(R)`, `I + A E_ij = ∏_(a,b) (I + A_ab E_((i,a),(j,b)))`. The factors
  commute, and all products of two of their off-diagonal parts vanish, because `j ≠ i`.
- **(⊇)** A transvection `I + r E_((p,a),(q,b))` with `p ≠ q` is `e_pq(r E_ab)`. For `p = q` and `a ≠ b`,
  choose `q' ≠ p`. With `X = I + (rE_ab)E_(pq')` and `Y = I + E_bb E_(q'p)`, one has
  `(rE_ab)E_bb = rE_ab` and `E_bb(rE_ab) = 0`. So `XY = (I + rE_ab E_pp)YX`, and
  `[X,Y] = I + r E_ab E_pp`, which is the in-block transvection.
- Elementary transvections generate `EL_(nk)(R)`.

Under the identification `GL_3(M_k(R_X)) = GL_(3k)(R_X)`, steps 2–4 give `EL_3(R_(X^(k))) ≅ EL_(3k)(R_X)`. An
isomorphism of groups carries the centre onto the centre, so the statement passes to quotients by centres.
