---
rg: 2
id: hughes-free-division-rings-pass-to-directed-unions-proof
kind: route
title: Glue the Hughes-free rings along their unique comparison maps and check the independence condition at a finite stage
target: hughes-free-division-rings-pass-to-directed-unions
requires:
  - fsp-graph-of-rings-and-linnell-extension-imports
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

## Proof

**Local indicability.** A finitely generated subgroup of `G` lies in some `G_i`, so it maps onto `Z` if nontrivial.

**Comparison maps are unique.** If `D` is an epic `R`-division ring and `f, g : D -> E` are ring maps into a
division ring that agree on `R`, then `f = g`: the set `{x : f(x) = g(x)}` is a subring containing `R`, and it is
closed under inverses because `f(x^(-1)) = f(x)^(-1) = g(x)^(-1) = g(x^(-1))`. So it contains `Div(R, D) = D`.

**The directed system.** For `i <= j`, the division closure of `k*G_i` in `D_j` is Hughes-free for `k*G_i` (item 1
of [[fsp-graph-of-rings-and-linnell-extension-imports]]). By Hughes uniqueness (item 1) there is a
`k*G_i`-isomorphism `D_i -> Div(k*G_i, D_j)`. Composed with the inclusion, it gives an injective map
`phi_ij : D_i -> D_j` over `k*G_i`. For `i <= j <= l`, both `phi_jl ∘ phi_ij` and `phi_il` are maps `D_i -> D_l` over
`k*G_i`, so they are equal by uniqueness. Let `D` be the directed colimit with maps `psi_i : D_i -> D`.

**`D` is a Hughes-free division ring of `k*G`.**
* *Division ring.* A directed colimit of division rings along injective maps is a division ring.
* *Injective.* `k*G = colim k*G_i`, each `k*G_i -> D_i` is injective, and the colimit is directed.
* *Epic.* Each `psi_i(D_i) = psi_i(Div(k*G_i, D_i))` lies in `Div(k*G, D)`, because the preimage of `Div(k*G, D)`
  under `psi_i` is a division subring of `D_i` containing `k*G_i`. So `Div(k*G, D) = D`.
* *Condition (HF).* Let `H <= G` be finitely generated, `N ⊴ H` with `H/N = <tN> ≅ Z`, and suppose
  `sum_n alpha_n t^n = 0` with finitely many nonzero `alpha_n in Div(k*N, D)`. Choose `i` with `H <= G_i`.
  - The union `U = ∪_(j >= i) psi_j(Div(k*N, D_j))` is directed, so it is a division subring of `D` containing
    `k*N`. So `Div(k*N, D) <= U`. Each term lies in `Div(k*N, D)` by the preimage argument above, so equality holds.
  - Hence there is one `j >= i` with every `alpha_n = psi_j(beta_n)`, `beta_n in Div(k*N, D_j)`, and
    `sum_n beta_n t^n = 0` in `D_j` because `psi_j` is injective.
  - Condition (HF) in `D_j`, for `H <= G_j`, gives `beta_n = 0`, so `alpha_n = 0`.

**Locally free groups.** Every finitely generated subgroup is free, hence residually torsion-free nilpotent, and
has a Hughes-free division ring by item 2 of the imports. Apply the claim to the directed family of finitely
generated subgroups. QED
