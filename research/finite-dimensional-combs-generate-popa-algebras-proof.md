---
rg: 2
id: finite-dimensional-combs-generate-popa-algebras-proof
kind: route
title: Teeth of the comb are exact local quantization corners, separation makes each stage residually finite-dimensional, and a nonzero ideal meets a simple tooth algebra and so contains a full projection
target: finite-dimensional-combs-generate-popa-algebras
requires: []
artifacts:
  - research/artifacts/sk-popa-lgx-plan-2026-09-13.md
---

Complete proof (sk-popa-lgx, 2026-09-13). Notation as in the target claim. `A_∞ = ⋃_i A_i` is norm dense in `A`.

**Step 1: each `A_i` is residually finite-dimensional, and `A` is quasidiagonal.**
- For `j ≥ i`, `e_j ∈ A_{j+1}` commutes with `A_j ⊇ A_i`. So `ρ_j(x) = e_jxe_j` is a unital *-homomorphism `A_i → e_jA_je_j`, which is finite-dimensional by (C1). Multiplicativity: `e_jxe_jye_j = e_jxye_j`, since `e_j` commutes with `y`.
- By (C2), `⊕_{j≥i} ρ_j` is injective on `A_i`, so `A_i` is residually finite-dimensional, hence quasidiagonal.
- `A` is an inductive limit of quasidiagonal algebras with injective connecting maps, so `A` is quasidiagonal: quasidiagonality is a local condition and passes to such limits.

**Step 2: local quantization.** Let `𝔉 ⊆ A` be finite and `η > 0`.
- Choose `i` and `x′ ∈ A_i` with `‖x − x′‖ < η/3` for each `x ∈ 𝔉`, and put `e = e_i`, `B = e_iA_ie_i`.
- `B` is a finite-dimensional C*-subalgebra with unit `e`. It lies in `A`, because `e_i ∈ A` and `A_i ⊆ A`, and it is nonzero because `e_i ≠ 0`; a zero `e_i` would contradict (C3).
- Since `[x′, e] = 0`, `‖[x,e]‖ ≤ 2‖x − x′‖ < η`.
- `ex′e ∈ B` gives `dist(exe, B) ≤ ‖e(x − x′)e‖ < η`.

**Step 3: simplicity.** Let `J ⊆ A` be a nonzero closed two-sided ideal.
- **Some `J ∩ A_i` is nonzero.** Let `q: A → A/J` be the quotient map. The induced map `A_i/(J∩A_i) → A/J` is an injective *-homomorphism, hence isometric. If every `J ∩ A_i` were `0`, `q` would be isometric on each `A_i`, hence on `A_∞` and, by density, on `A`, so `J = 0`.
- Choose `i` and a nonzero `x ∈ J ∩ A_i`. By (C2) there is `j ≥ i` with `e_jxe_j ≠ 0`.
- `K = J ∩ e_jA_je_j` is a two-sided ideal of the finite-dimensional algebra `D = e_jA_je_j`:
  - for `a = e_ja′e_j`, `a′ ∈ A_j`, and `k ∈ K`, `ak = e_ja′e_jk ∈ J`, and `ak ∈ D` because `e_j` commutes with `A_j` and `k ∈ D`;
  - likewise `ka ∈ J ∩ D`.
- `e_jxe_j ∈ J`, since `e_j ∈ A` and `x ∈ J`, and it lies in `D`. So `K ≠ 0`.
- By (C1), `D` is simple, so `K = D ∋ e_j` and `e_j ∈ J`.
- By (C3), `1 = Σ_l v_le_jv_l* ∈ J`, so `J = A`. `A` is unital and nonzero, so it is simple.

With Steps 2 and 3, `A` is a Popa algebra. ∎
