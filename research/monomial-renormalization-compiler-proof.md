---
rg: 2
id: monomial-renormalization-compiler-proof
kind: route
title: Product codes multiply odometer heights; a global block rotation composed with one code realizes a companion matrix; then compile
target: monomial-renormalization-compiler-gives-dilation-groups-in-nv
requires:
  - brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups
  - odd-smart-induced-map-has-height-m-renormalization
---

Write `T = T_m`, `e = e^{(m)}` for a fixed odd `m`, so `T^m e_i = e_i T` (odometer identity).

**One cycle (companion block).** Take `d` copies of `C^2`, so `X = (C^2)^d = C^{2d}`, and let `T_j` be
`T` acting on block `j` (identity elsewhere). The `T_j` commute and generate `Z^d`: a relation
`∏ T_j^{a_j} = 1` restricts to `T^{a_j} = 1` on block `j`, and `T` has infinite order.

Let `ρ(x_1, …, x_d) = (x_d, x_1, …, x_{d-1})` be the block rotation (a coordinate permutation), and
`ê_i` be `e_i` on block 1. Put `E_i = ê_i ∘ ρ`. The images `E_i X = X_i × (C^2)^{d-1}` partition `X`,
so `E` is an `m`-ary twisted brick code (item 3 of the compiler claim, with the single permutation `ρ`).

Compute `δ_E(T_j) = ⊔_i E_i T_j E_i^{-1}`. Since `E_i^{-1}(y) = (y_2, …, y_d, e_i^{-1} y_1)`:
- For `j < d`: `T_j` acts on entry `j`, which is `y_{j+1}`. Then `E_i` rotates back, so
  `E_i T_j E_i^{-1} = T_{j+1}` on `E_i X`, for every `i`. So `δ_E(T_j) = T_{j+1}`.
- For `j = d`: `T_d` acts on `e_i^{-1} y_1`. Then `E_i` returns `e_i T e_i^{-1} y_1` to block 1. So
  `δ_E(T_d) = (⊔_i e_i T e_i^{-1})` on block 1, which is `T^m` on block 1, i.e. `T_1^m`.

So `δ_E` restricted to `⟨T_j⟩ = Z^d` is the companion matrix of `x^d - m`, and `⟨T_j⟩` is
`δ_E`-closed.

**Several cycles.** Put the cycles on disjoint block sets. Use one global permutation (the product of
the block rotations) and the product code `E_{(i_1,…,i_r)} = ∏_c E^{(c)}_{i_c}`, of arity `∏ m_c`.
Each factor commutes with the other cycles' machines. So `δ_E` acts on cycle `c` exactly as `E^{(c)}`
does: it is block diagonal with the companion blocks. If every `d_c = 1`, no rotation occurs and the
code is untwisted brick-local.

**Compile.** Apply `brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups` (item 3 for the
twisted case) to `H = Z^d` and `δ_E = M`. This gives `Z^d *_M ↪ (2d+1)V ⋊ Sym(2d)`, and into `(2d+1)V`
if the code is untwisted.

**Identification.** For one block, send `T_j ↦ α^{j-1}` in `R = Z[x]/(x^d - m)`, `α = x`. Then `M` is
multiplication by `α`, since `α · α^{d-1} = m`. `M` is injective with cokernel of order `m`, and
`α^{-1} = α^{d-1}/m`. So `Z^d *_M = ⋃_n α^{-n} R ⋊ ⟨α⟩ = R[1/m] ⋊ ⟨α⟩`. Blocks add.

**Subgroups in the untwisted group.** For one block, `ρ^d = id`, so `t^d = g^d` lies in `(2d+1)V`
(products of `ρ`-conjugates of `g_0`). Also `δ_E^d = m·id`, so `⟨T_1, t^d⟩ = BS(1,m)`.

**Boone–Higman.** `(2d+1)V` is finitely presented, simple and MIF. `(2d+1)V ⋊ Sym(2d)` is a
finite-index overgroup of it, and so lies in `B_A`
(`fp-simple-highly-transitive-groups-satisfy-pbh`, `boone-higman-type-a-class-closed-under-finite-extensions`).
∎
