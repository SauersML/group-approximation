---
rg: 2
id: fpbs-mal-overgroup-is-free-by-cyclic
kind: claim
title: The ascending HNN overgroup of Gamma_mal is F_3 by Z with explicit monodromy, and Gamma_mal is the kernel of a boundary character over the common free kernel K
distinct_from:
  fpbs-mal-bernoulli-single-stage-floor: that is the open floor for the Bernoulli shift of Gamma_mal; this is a structure theorem for the overgroup M, and decides nothing about the floor.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that is the open fixed-price statement for groups with a bounded-cost normal subgroup; this exhibits M as an instance of it with N = F_3 and K = 3, and proves nothing about it.
  fpbs-mal-odometer-product-actions-have-cost-two: that computes costs of odometer products of Gamma_mal; this is group structure only, with no action.
artifacts:
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/semidirect.py
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/semidirect_out.txt
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/magnus.py
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/magnus_out.txt
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/fox.py
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/fox_out.txt
---

**ESTABLISHED** through `fpbs-mal-overgroup-is-free-by-cyclic-proof`.

Let `M = <a, b, t | [t, a], t b t^{-1} = b a b^{-2}>`, the ascending HNN
overgroup of `Gamma_mal`. Eliminating `a = b^{-1} t b t^{-1} b^2` gives
`M = <b, t | r>` with
`r = t b^-1 t b t^-1 b^2 t^-1 b^-2 t b^-1 t^-1 b`. Write characters of
`M^ab = Z^2` as `psi = (psi(b), psi(t))`, so `psi(a) = 2 psi(b)`.

1. **Free-by-cyclic.** `M ≅ F(u, v, w) ⋊_Θ <b>`, where `Θ` is conjugation by
   `b`:
   - `Θ: u ↦ v, v ↦ w, w ↦ v u^-1 v^2 w^-1`;
   - `Θ^-1: u ↦ u^2 v^-1 w^-1 u, v ↦ u, w ↦ v`.

   Here `t = v b` and `a = u v^-1 b^2`. The fibre `F_3` is `ker (1,1)`,
   with `v = t b^-1`, `u = b^-1 v b` and `w = b v b^-1`.
2. **Common kernel.** `K := [M, M] = ker(ε: F_3 → Z)`, with
   `ε(u) = ε(v) = ε(w) = 1`. So `K ≅ F_∞`, and every character kernel is
   `K ⋊ <c>` for a lift `c` of a generator of `ker(psi) ⊂ Z^2`:
   - `Gamma_mal = ker (0,1) = K ⋊ <b>`, with stage `<a, b> = <u v^-1, b>`;
   - `N_1 := ker (1,0) = K ⋊ <t>`;
   - `N_2 := ker (1,2) = K ⋊ <t b^-2>`;
   - `F_3 = ker (1,1) = K ⋊ <t b^-1>`.
3. **Alexander data (computed).** Up to a unit,
   `Δ_M = x^2 + x + y − 1` (`x = b`, `y = t`). Its Newton polygon is the
   triangle `(0,0), (2,0), (0,1)`, with
   `width(psi) = max{0, 2β, τ} − min{0, 2β, τ}` at `psi = (β, τ)`. The
   width is `1` at `(0,1)`, which matches `β_1^(2)(Gamma_mal) = 1`. It is
   `2` at both `(1,0)` and `(1,2)`.

**Remark (cited, not load-bearing).** For `psi = (1, k)`, the Magnus rewrite
of `r` has unique extreme indices exactly when `k ∉ {0, 2}`. In that case
`ker psi` is free of rank `width + 1`, verified for `k = −5..6`
(`magnus_out.txt`). By Brown's criterion (Invent. Math. 90 (1987),
Thm 4.2), the non-fibred rational rays are those on the three lines
`β = 0`, `τ = 0` and `τ = 2β`. They are the kernels `Gamma_mal`, `N_1` and
`N_2`, and each is an ascending union of free stages that is not finitely
generated. This remark is not used by any ESTABLISHED statement.
