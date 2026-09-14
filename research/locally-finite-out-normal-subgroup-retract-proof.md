---
rg: 2
id: locally-finite-out-normal-subgroup-retract-proof
kind: route
title: Centerless normal subgroups with locally finite Out are retracts of finite-index subgroups
target: centerless-normal-subgroups-with-locally-finite-out-of-fp-are-fp
requires: []
---

Let `φ: G → Aut(N)` be conjugation and `π: Aut(N) → Out(N)` the quotient.

1. **Finite index.** `G` is finitely generated, so `π∘φ(G)` is a finitely generated subgroup of
   `Out(N)`, hence finite. So `G₀ = ker(π∘φ)` has finite index in `G`, and it is finitely
   presented (Reidemeister–Schreier; finite-index subgroups of finitely presented groups are
   finitely presented). Also `N ⊆ G₀`, since conjugation by elements of `N` is inner.
2. **Retraction.** For `g ∈ G₀` there is `n_g ∈ N` with `g x g⁻¹ = n_g x n_g⁻¹` for all `x ∈ N`,
   and `n_g` is unique because `Z(N) = 1`. Both `n_{gh}` and `n_g n_h` induce conjugation by `gh`
   on `N`, so uniqueness gives `n_{gh} = n_g n_h`. So `r: G₀ → N`, `g ↦ n_g`, is a homomorphism,
   and `r(x) = x` for `x ∈ N`.
3. **Retracts of finitely presented groups are finitely presented.** Write `G₀ = ⟨S | R⟩` with
   `S, R` finite, `i: N → G₀` the inclusion, and for each `s ∈ S` choose a word `w_s` in `S`
   representing `i(r(s))`. Let `K` be the normal closure of `{s⁻¹ w_s : s ∈ S}` and
   `p: G₀ → G₀/K`.
   - `K ⊆ ker r`, since `r(s⁻¹ w_s) = r(s)⁻¹ r(i(r(s))) = 1`. So `r` induces `r̄: G₀/K → N`.
   - In `G₀/K` each generator `p(s)` equals `p(i(r(s)))`, so `p∘i: N → G₀/K` is surjective.
   - `r̄∘p∘i = r∘i = id_N`, so `p∘i` is injective.
   Hence `N ≅ G₀/K = ⟨S | R ∪ {s⁻¹ w_s : s ∈ S}⟩`, a finite presentation.
