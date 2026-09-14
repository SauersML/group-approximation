---
rg: 2
id: residually-finite-groups-are-lef-proof
kind: route
title: A finite quotient that separates the finitely many differences of a finite set is a local embedding
target: residually-finite-groups-are-lef
requires: []
---

Let `Γ` be residually finite and let `F ⊆ Γ` be finite.
1. The set `D = {a^{-1}b : a, b ∈ F, a ≠ b}` is finite and does not contain `1`.
2. For each `d ∈ D` choose a normal subgroup `N_d` of finite index with `d ∉ N_d`. Put `N = ⋂_{d∈D} N_d`. It is normal
   and of finite index (take `N = Γ` if `D` is empty).
3. The quotient map `π: Γ → Q = Γ/N` is a homomorphism, so it preserves every product, in particular those that stay
   in `F`.
4. It is injective on `F`: if `π(a) = π(b)` with `a ≠ b` in `F`, then `a^{-1}b ∈ N ⊆ N_{a^{-1}b}`, contradicting step 2.

So `π|_F` embeds `F` injectively into the finite group `Q` and preserves products that stay in `F`. This is the
definition of LEF.
