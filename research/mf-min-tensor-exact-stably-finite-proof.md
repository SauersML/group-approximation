---
rg: 2
id: mf-min-tensor-exact-stably-finite-proof
kind: route
title: Embed the tensor product in the matrix corona over C and straighten almost-isometries block by block
target: mf-min-tensor-exact-stably-finite-is-stably-finite
requires: []
---

Let `A ⊂ Q := ∏_n M_{k_n}/⊕_n M_{k_n}` be MF, and let `C` be exact with stably
finite unitization `C̃`. Full details are in
research/artifacts/uct-nuclear-proper-isometry-2026-09-12.md §2.

1. **Corona embedding.** Steps 1--6 of `mf-min-tensor-exact-mf-proof` use only
   exactness of `C`. They give
   `A ⊗_min C ⊂ Q ⊗_min C ↪ ∏_n M_{k_n}(C)/⊕_n M_{k_n}(C)`. That quotient embeds in
   `D := ∏_n M_{k_n}(C̃)/⊕_n M_{k_n}(C̃)`, since norm-null sequences are the same in
   both products.
2. **Straightening.** Let `E = ∏E_n/⊕E_n` with every `E_n` finite and unital. If
   `v*v = 1` in `E`, lift `v` to `(V_n)` with `‖V_n*V_n − 1‖ → 0`, and put
   `W_n = V_n(V_n*V_n)^{-1/2}`, an exact isometry with `‖W_n − V_n‖ → 0`.
   Finiteness gives `W_nW_n* = 1`, so `‖V_nV_n* − 1‖ → 0` and `vv* = 1`.
3. **Stable finiteness of `D`.** `M_m(D) ≅ ∏_n M_{mk_n}(C̃)/⊕_n M_{mk_n}(C̃)`, and
   every block is finite because `C̃` is stably finite. By step 2 every `M_m(D)` is
   finite.
4. **Pass to the subalgebra.**
   - If `A ⊗_min C` is unital with unit `e`, it is a unital subalgebra of the corner
     `eDe`, which is stably finite. In `M_m(D)`, `w + (1−e) ⊗ 1_m` is an isometry,
     hence unitary.
   - Otherwise its unitization is `A ⊗_min C + ℂ1_D ⊂ D`.

   Either way `A ⊗_min C` is stably finite.
5. **The nuclear faithful-trace case.** A faithful tracial state `τ` on `C` extends
   to `τ̃(λ1 + c) = λ + τ(c)` on `C̃`.
   - `τ̃` is faithful. In its GNS representation `π`, the inequality
     `τ̃(y*x*xy) ≤ ‖y‖² τ̃(x*x)` shows `τ̃(x*x) = 0 ⇒ π(x) = 0`.
   - `π` is faithful on `C̃`, because `π(C) ≅ C` has no unit.
   - So `tr_m ⊗ τ̃` is faithful on `M_m(C̃)`, and `C̃` is stably finite.
