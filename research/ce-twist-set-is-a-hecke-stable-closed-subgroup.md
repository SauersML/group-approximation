---
rg: 2
id: ce-twist-set-is-a-hecke-stable-closed-subgroup
kind: claim
title: The Connes-embeddable twists of a finitely presented group form a closed subgroup with a rational Hecke-stable Lie algebra
distinct_from:
  maslov-ce-parameter-set-is-a-closed-subgroup: that proves closedness on the single Maslov circle of Sp4(Z); this treats the whole multiplier torus of any finitely presented group and adds restriction, tensor induction and Hecke stability.
  sp4-finite-index-scalar-data-iff-hyperlinear-covers: that relates positive dimension of E_CE to hyperlinear covers on finite-index subgroups of Sp4(Z); this proves the structural transport properties that are independent of Sp4 and relates the full Lie algebra to hyperlinearity of all finite cyclic covers.
  torsion-dense-schur-multiplier-compiles-twisted-nonce: that compiles one non-CE twist into a non-CE torsion twist; this describes the connected part of the CE set and its symmetry under commensurators.
---

**ESTABLISHED** (elementary; no priority is claimed).  Let `Gamma` be
finitely presented, `e(t)=exp(2 pi i t)`, and

```text
E_CE(Gamma) = { [omega] in H^2(Gamma,T) : L_omega(Gamma) is Connes embeddable }.
```

Let `T_0` be the identity component of `H^2(Gamma,T)`, a torus of dimension
`b=b_2(Gamma)`, with Lie algebra `H^2(Gamma,R)` and lattice given by integral
classes.  Then:

1. **(HS1)** `E_CE(Gamma)` is a subgroup, and `E_CE(Gamma) cap T_0` is closed.
   Its identity component `E^0` is a subtorus; its Lie algebra `W(Gamma)` is a
   rational subspace of `H^2(Gamma,R)`.
2. **(HS2)** For `Lambda <= Gamma` of finite index, `[omega] in E_CE(Gamma)` iff
   `res[omega] in E_CE(Lambda)`.
3. **(HS3)** For infinite `Lambda <= Gamma` of finite index, the tensor-induction
   homomorphism `TI : H^2(Lambda,T) -> H^2(Gamma,T)` (cochain formula in the
   route) maps `E_CE(Lambda)` into `E_CE(Gamma)`.
4. **(HS4)** Group isomorphisms transport `E_CE`.
5. **(HS5)** Let `Gamma <= G` be infinite and `g in G` commensurate `Gamma`.
   The Hecke correspondence `T_g = TI o (c_g)^* o res`, taken through
   `Gamma cap g^(-1) Gamma g`, maps `E_CE(Gamma)` into itself and `E^0` into
   `E^0`.  Its derivative preserves `W(Gamma)`.
6. **(HS6)** `W(Gamma) = H^2(Gamma,R)` iff every finite cyclic central
   extension `E_x^(n)` of `Gamma`, for `x in H^2(Gamma,Z)` and `n >= 1`, is
   hyperlinear.  More precisely, an integral `x` lies in `W(Gamma)` iff all
   `E_x^(n)` are hyperlinear.

**Instance.**  `Gamma(4) <= Sp_4(Z)` is finitely presented (finite index in
a finitely presented group).  Hoffman--Weintraub, *Cohomology of the Siegel
modular group of degree two and level four*, Theorem 1.2 (p. 3, read from
the PDF): "The Betti numbers h^i = dim H^i(Gamma(4), Q) of the principal
congruence subgroup of level 4 in Sp_4(Z) are 1, 0, 118, 1112, 481 for i = 0,
..., 4 and 0 for all other values."

So `W(Gamma(4))` is a rational subspace of `R^118`, stable under every Hecke
correspondence `T_g` with `g in Sp_4(Q)`, since `Sp_4(Q)` commensurates
`Sp_4(Z)`.  A single rational Hecke piece of `H^2(Gamma(4),R)` outside `W`
yields a non-hyperlinear finitely presented `E_x^(n)`.  Deciding this is
exactly `non-hyperlinear-group` restricted to the covers of `Gamma(4)`; this
claim proves no non-embeddability.
