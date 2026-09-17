---
rg: 2
id: simple-product-completions-block-regular-tree-actions-proof
kind: route
title: Discard the small factors, then compare level-stabilizer quotients with the finite quotients of a product of large simple groups
target: simple-product-completions-block-regular-tree-actions
requires: []
---

Notation. `ι : Γ -> Γ^` is the canonical map; it is injective because `Γ` is
residually finite. For `m >= 1`, `V_m` is the class of finite groups all of
whose composition factors have order at most `m`. By Jordan--Hölder, a
composition factor of a subgroup or a quotient of a finite group `G` is a
subquotient of a composition factor of `G`. So `V_m` is closed under subgroups
and quotients.

**Step 0 (the extension fact).** Let `W` be an open subgroup of `Γ^` and
`Δ = ι^(-1)(W)`. Every homomorphism `f` from `Δ` onto a finite group `P`
extends to a continuous homomorphism `F` from `W` onto `P` with `F ∘ ι = f`.

- `Δ` has finite index in `Γ`, since `W` has finite index in `Γ^`.
- `N = ker f` has finite index in `Γ`. Let `N_0` be its normal core in `Γ`, of
  finite index. Let `π : Γ^ -> Γ/N_0` be the continuous extension of the
  quotient map. `K = ker π` is open and normal, with `ι^(-1)(K) = N_0`.
- `ι(Γ)` is dense. For `w in W`, the open set `wK ∩ W` contains some `ι(γ)`,
  and `γ in Δ`. Put `F(w) = f(γ)`. If `ι(γ)K = ι(γ')K` then `γ^(-1)γ' in N_0 <= N`,
  so `F` is well defined. It is a homomorphism, constant on cosets of
  `K ∩ W` and hence continuous, and `F ∘ ι = f` on `Δ`. It is onto because
  `f` is.

**Step 1 (level quotients).** Suppose `Γ <= Aut(T_d)`. For `n >= 1` the
stabilizer of level `n` has quotient embedded in the automorphism group of the
first `n` levels. That group is the `n`-fold iterated wreath product of `S_d`,
and it has a normal series whose factors are direct powers of `S_d`. Every
composition factor of a subgroup of a direct power of `S_d` is a composition
factor of a subgroup of `S_d`, by projecting to the coordinates one at a time.
So every such level quotient of every subgroup of `Γ` lies in `V_(d!)`. If a
subgroup `Δ` of `Γ` is nontrivial, some element moves some vertex of some level
`n`, and the level-`n` quotient of `Δ` is nontrivial.

**Step 2 (discard small factors).** Fix `m`. The set `E = { i : |S_i| <= m }` is
finite by hypothesis. Let `U_m` be the closed subgroup of `U` whose coordinates
in `E` are trivial. Its index in `U` is `prod_(i in E) |S_i|`, so it is open in
`U` and hence in `Γ^`. Put `Δ_m = ι^(-1)(U_m)`, of finite index in `Γ`.

`ι(Δ_m) = ι(Γ) ∩ U_m` is dense in `U_m`, because `U_m` is open and `ι(Γ)` is
dense. `U_m ≅ prod_(i notin E) S_i` is infinite. A finite dense subset of a
Hausdorff space is the whole space, so `Δ_m` is infinite.

**Step 3 (finite quotients of `Δ_m`).** Let `f : Δ_m -> P` be onto, with `P` finite
in `V_m`. By Step 0 it extends to a continuous `F : U_m -> P` onto `P`.
- `ker F` is open. So it contains a basic neighbourhood of `1`: the subgroup
  of elements whose coordinates in some finite set `E'` (disjoint from `E`) are
  trivial. Hence `P` is a quotient of the finite product `prod_(i in E') S_i`.
- A normal subgroup `M` of a finite product `prod_(i in E') S_i` of nonabelian
  simple groups is a subproduct. If the projection of `M` to `S_j` is nontrivial,
  pick `x in M` with `x_j != 1`. Then `[x, S_j]` is a nontrivial normal subgroup
  of `S_j` inside `M`, so `S_j <= M`. Hence `M` is the product of the factors
  onto which it projects nontrivially, and the quotient is `prod_(i in E'') S_i`
  for some `E'' <= E'`.
- If `P != 1`, then `P` has a composition factor `S_i` with `i notin E`, of order
  `> m`, so `P notin V_m`. Hence `P = 1`.

This proves the sharper form. `Δ_m` is infinite and has no nontrivial quotient
in `V_m`.

**Step 4 (conclusion).** If `Γ <= Aut(T_d)`, take `m = d!`. By Step 1 the
nontrivial group `Δ_m` has a nontrivial level quotient in `V_(d!)`, which
contradicts Step 3. So `Γ` embeds in no `Aut(T_d)`.

Condition (N1) for a given `d` asks that `Γ` be residually `W_d`, and `W_d`
is contained in `V_(d!)`. A nontrivial residually `W_d` subgroup `Δ_m` would
have a nontrivial quotient in `V_(d!)`. So (N1) fails for every `d` as well. `∎`
