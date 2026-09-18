---
rg: 2
id: finitely-presented-divisible-ring-engine-proof
kind: route
title: Shift-and-counter relations force a right inverse of each integer, and a faithful operator model shows the ring is nonzero
target: finitely-presented-divisible-ring-engine
requires: []
artifacts:
  - experiments/char-zero-projective-host-screens-2026-09-17/divisible_ring_engine_model.py
---

Write `q = wv` and `o = 1 - q`. By R2, `q` is idempotent.

**(i) Commutation with the shift.**
- `bw = b w (vw) = (bq) w = (qb) w = w (vbw) = w(b+1)`, using R2, R4 and R5.
- By induction, `b w^k = w^k (b+k)` for all `k >= 0`.

**(ii) Right inverse of `b+k`.** Put `c_k = v^k a w^k`. Then
`c_k (b+k) = v^k a w^k (b+k) = v^k a b w^k = v^k w^k = 1`, using (i), R7 and R2.

**(iii)** By R6, `(b+k) o = bo + ko = o + ko = (k+1) o`.

**(iv)** Put `x_k = c_k o`. The integer `k+1` is central, so
`(k+1) x_k = c_k (k+1) o = c_k (b+k) o = o`, by (iii) and (ii).

**(v)** By R1 and R3, `s o t = st - s q t = 1 - (1 - q) = q`.

**(vi)** Put `y_k = x_k + s x_k t`. Then `(k+1) y_k = o + s o t = o + q = 1`.
- Since `k+1` is central, `y_k` is a two-sided inverse of `k+1`.
- The inverse `z` of a central element `m` is central: `yz = z m y z = z y m z = zy`.
- Also `-1` is a unit.
- So every nonzero integer is a central unit, and `Z -> D` extends to a ring map `Q -> Z(D)`.

**(vii) `D != 0`.**
- Let `V` be the `Q`-vector space with basis `e_x`, `x in Z \ {0}`.
- Let `σ` be the involution `2m <-> 2m-1`, `-2m <-> -(2m-1)` (`m >= 1`). It swaps even and odd integers.
- Define the operators:
  - `s = t = (e_x -> e_{σ(x)})`;
  - `w e_x = e_{2x}`;
  - `v e_{2x} = e_x` and `v e_{odd} = 0`;
  - `b e_x = (ν_2(x)+1) e_x`;
  - `a e_x = e_x/(ν_2(x)+1)`.
- The relations hold on every basis vector:
  - R1: `σ^2 = id`.
  - R2: clear from the definitions of `v` and `w`.
  - R3: `q` is the projection onto the even basis vectors, and conjugating it by the parity swap `σ` gives the projection onto the odd ones, which is `1 - q`.
  - R4: `b` is diagonal.
  - R5: `vbw e_x = (ν_2(2x)+1) e_x = (b+1) e_x`.
  - R6: `b` acts as `1` on odd `x`.
  - R7: `a` is the inverse diagonal.
- This gives a unital ring map `D -> End_Q(V)` with `V != 0`, so `D != 0`. Every ring map `Q -> D` into a nonzero ring is injective.
- The artifact script checks all seven relations and `(k+1) y_k = 1` for `k = 0..12` on the window `[-257, 257] \ {0}`.

**(viii) Coproduct corollary.**
- `R *_Z D` is presented by the union of the generators and relations of `R` and `D`, so it is finitely presented. It is a `Q`-algebra because `D` is.
- For injectivity, let `M = (R ⊗_Z Q) ⊗_Q V`.
  - Let `R` act on `M` by `r ↦ L_r ⊗ id`, and `D` act by `id ⊗ ρ`, where `ρ` is the model of (vii).
  - Both actions are unital ring maps into `End_Z(M)`. By the universal property of the coproduct, they give a ring map `R *_Z D -> End_Z(M)` whose restriction to `R` is `r ↦ L_r ⊗ id`.
  - This restriction is injective. `R -> R ⊗ Q` is injective because `R` is torsion-free. Also `(L_r ⊗ id)(1 ⊗ e_1) = r ⊗ e_1`, which is nonzero for `r ⊗ 1 != 0`.
- So `R -> R *_Z D` is injective. ∎
