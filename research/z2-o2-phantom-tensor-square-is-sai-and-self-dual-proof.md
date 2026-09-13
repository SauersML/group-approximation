---
rg: 2
id: z2-o2-phantom-tensor-square-is-sai-and-self-dual-proof
kind: route
title: Multiplicativity of θ gives the crossed-product form, Green–Takai at the diagonal gives self-duality, averaging w⊗w gives strong approximate innerness, and the O_2 criteria give the Rokhlin forms
target: z2-o2-phantom-tensor-square-is-sai-and-self-dual
requires:
  - zp-restriction-trivial-splits-cellular-plus-phantom
  - z2-o2-actions-anti-inner-and-o3-rokhlin-criterion
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
  - z2-odd-commutator-below-half-forces-commuting-towers
artifacts:
  - research/artifacts/uct-z2-square-zero-phantoms-2026-09-13.md
---

Full derivation: the artifact, §2. Summary follows.

1. **Categorical form.** Items 1 and 6 of `zp-restriction-trivial-splits-cellular-plus-phantom` give
   `θ_(D⊗D) = θ_D ⊗ θ_D = 1`. By item 2 there, `(D ⊗ D) ⋊ G ≃_KK 0` iff `1 − θ = 0` is invertible in
   `KK^G(D ⊗ D, D ⊗ D)`, that is, iff `D ⊗ D ≃ 0`.
2. **Self-duality.**
   - `Res D̂ = D ⋊ G ≃ 0`, and `D̂ ⋊ Ĝ ≃_KK Res D ≃ 0` by Takai.
   - Write `D ≃_(KK^G) B ⋊ Ĝ` with `B = D̂`. Then the `G × G`-algebra `D ⊠ D` is
     `(B ⊠ B) ⋊ (Ĝ × Ĝ)` up to stabilization.
   - Green–Takai with `L = Δ_G ≤ G × G` gives `L^⊥ = {(χ, χ̄)} = Δ_Ĝ`, since `χ̄ = χ` on `Z/2`. So
     `(D ⊗ D) ⋊_(α⊗α) G ~_M (B ⊗ B) ⋊_(β⊗β) Ĝ`.
   - Morita equivalence preserves contractibility. Apply step 1 to `D` and to `D̂`.
3. **Strong approximate innerness on O_2.**
   - Item 2(a) of `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` gives unitaries `w_n` with
     `‖σ(w_n) + w_n‖ → 0` and `w_n* a w_n → σ(a)`.
   - For `u_n = w_n ⊗ w_n`,
     `(α ⊗ α)(u_n) − u_n = (σw_n + w_n) ⊗ σw_n − w_n ⊗ (σw_n + w_n)`, which has norm
     `≤ 2‖σ(w_n) + w_n‖`.
   - The polar parts of the invariant averages `(u_n + (α ⊗ α)(u_n))/2` are invariant unitaries
     `z_n` with `‖z_n − u_n‖ → 0`.
   - `Ad(z_n*) → α ⊗ α` pointwise, on elementary tensors and then by density.
4. **Rokhlin forms.**
   - `α ⊗ α` is pointwise outer (standard fact).
   - `≃ 0` iff Rokhlin: item 2 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`.
   - `≃ 0` iff the crossed product is KK-contractible: step 1. For a unital Kirchberg algebra that is
     iff it is `≅ O_2`, by Kirchberg–Phillips.
   - Rokhlin gives `2[1] = 0` and a unital `O_3`, by item 2(b) of the O_2 node.
   - Conversely, `2[1] = 0` iff `(α ⊗ α)^` is strongly approximately inner (item 1 of that node).
     That gives the Rokhlin property, by item 3(b) of
     `z2-odd-commutator-below-half-forces-commuting-towers`.
5. **Calibration.** `τ(O_2) ≃_(KK^G) 0`, so `(O_2, α) ⊗ τ(O_2) ≃ 0`. `α ⊗ id_(O_2)` is pointwise
   outer, so it is Rokhlin by item 2 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`.
