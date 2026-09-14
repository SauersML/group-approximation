---
rg: 2
id: simple-kazhdan-group-gives-property-t-factor-in-r-omega-proof
kind: route
title: Proof — ICC gives a factor, Connes–Jones gives (T), hyperlinearity gives the R^omega embedding
target: simple-kazhdan-group-gives-property-t-factor-in-r-omega
requires:
  - continuum-many-simple-kazhdan-lef-groups
  - infinite-simple-groups-are-icc
---
`continuum-many-simple-kazhdan-lef-groups` gives that `G_X` is infinite, finitely
generated, simple, has property (T), and is LEF (hence sofic and hyperlinear).

By `infinite-simple-groups-are-icc`, `G_X` is ICC, so `L(G_X)` is a separable II_1
factor. Property (T) of the group passes to the factor: for an ICC property (T)
group, `L(G)` is a property (T) II_1 factor (Connes--Jones, *Property T for von
Neumann algebras*, Bull. London Math. Soc. 17 (1985), 57--62).

Hyperlinearity of `G_X` means `G_X ⊂ U(R^ω)`; for any group `Γ`, `Γ` is hyperlinear
iff `L(Γ)` is isomorphic to a von Neumann subalgebra of `R^ω` (Ozawa, *About the
QWEP conjecture*, Prop. 7.1). So `L(G_X)` embeds in `R^ω`.

Brown's von Neumann formulation asks for a separable McDuff factor. The witness is
`L(G_X) ⊗̄ R` (`brown-mcduff-witness-for-simple-kazhdan-lef-group`).

Repair (2026-09-13, sk-operator-algebras): the earlier closing sentence ("`R^ω` is
McDuff") used a non-separable algebra and is withdrawn. The target claim does not use it.
