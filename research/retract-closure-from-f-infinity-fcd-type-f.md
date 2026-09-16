---
rg: 2
id: retract-closure-from-f-infinity-fcd-type-f
kind: route
title: "Retracts of type F groups are finitely presented of type FP, so the F_infinity hole makes them type F"
target: retracts-of-type-f-groups-are-of-type-f
requires: [f-infinity-groups-of-finite-cd-are-of-type-f]
artifacts:
  - research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md
---

Standard facts (S1), (S2) and (S5) are as listed in
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof`. The argument below
is that route's (1)⇒(3) step, which uses only `r∘i = id`.

Let `Γ` be of type F, with `i: G → Γ`, `r: Γ → G` and `r∘i = id_G`.

1. **Finite presentation.** Let `Γ = ⟨X | R⟩` be finite, and let `e = i∘r`.
   `e` is idempotent and `ker e = ker r`, since `i` is injective. Let `N` be
   the normal closure of `{x⁻¹e(x) : x ∈ X}`.
   - `N ⊆ ker e`, since `e(x⁻¹e(x)) = e(x)⁻¹e(e(x)) = 1`.
   - Let `S = {g ∈ Γ : g⁻¹e(g) ∈ N}`. It contains `X`.
   - `S` is closed under products: `(gh)⁻¹e(gh) = h⁻¹(g⁻¹e(g))h · h⁻¹e(h)`.
   - `S` is closed under inverses: `g e(g)⁻¹ = g (g⁻¹e(g))⁻¹ g⁻¹`, because
     `N` is normal.
   - So `S = Γ`, and for `g ∈ ker e`, `g⁻¹ = g⁻¹e(g) ∈ N`.

   Thus `G ≅ Γ/ker r = ⟨X | R, x⁻¹e(x) (x ∈ X)⟩` is finitely presented.
2. **`FP_∞`.** For a `ZG`-module `M` let `r^*M` be `M` regarded as a
   `ZΓ`-module via `r`. There are maps `i_*: H_k(G;M) → H_k(Γ;r^*M)` (allowed
   since `i^*r^*M = M`) and `r_*: H_k(Γ;r^*M) → H_k(G;M)`. They are natural
   in `M` and compose to `(r∘i)_* = id`. Since `r^*∏M_λ = ∏r^*M_λ`, the
   Bieri–Eckmann comparison map (S5) for `G` at `(M_λ)` is a retract, in the
   arrow category, of the one for `Γ` at `(r^*M_λ)`. Retracts of bijections
   are bijections, and retracts of surjections are surjections. `Γ` is `FP_∞`,
   so `G` is `FP_∞`.
3. **Finite cd.** `cd G ≤ cd Γ < ∞`, since `i` embeds `G` as a subgroup.
4. **Conclusion.** By (S1), `G` is of type `F_∞`, with finite cd. By
   `f-infinity-groups-of-finite-cd-are-of-type-f`, `G` is of type F. QED
