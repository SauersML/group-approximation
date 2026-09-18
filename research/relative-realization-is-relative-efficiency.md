---
rg: 2
id: relative-realization-is-relative-efficiency
kind: claim
title: For G with a finite 2-dimensional K(G,1) and finitely presented H of gd at most 2, RP(H,G) holds iff G has a finite relative presentation over H with |R| - |T| = chi(G) - chi(H); pi_2 of every presentation is stably free of rank chi(Y) - chi(G), and in a one-relator group the relative defect is at most (2-cells of a core of X_H) - 1
distinct_from:
  two-cell-injective-maps-realize-relative-eg-pairs: that characterizes RP(H,G) by 2-cell-injective maps into one fixed K(G,1). This result replaces the map by a numerical invariant, the relative defect rho(H,G) of arbitrary finite 2-complexes containing a K(H,1). In the one-relator case its w-disc criterion is exactly the case n(core) = 1 of the bound rho <= n(core) - 1.
  relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two: that converts RP into a gd-2 question for an aleph_1 amalgam. This converts RP for finite-type pairs into a relative deficiency (efficiency) equation, with no uncountable construction.
artifacts: []
---

**ESTABLISHED** through `relative-realization-is-relative-efficiency-proof`. Unreviewed.

**Setting.** `G` has a finite 2-dimensional `K(G,1)`. `H <= G` is finitely presented with a finite
2-dimensional `K(H,1)`. `RP(H,G)` means that some 2-dimensional `K(G,1)` has an aspherical
subcomplex inducing `H <= G`. A *relative presentation* of `(G,H)` is a finite connected
2-complex `Y` containing a finite 2-dimensional `K(H,1)` `K` as a subcomplex, such that
`pi_1 Y ≅ G` and `pi_1 K -> pi_1 Y` is the inclusion `H <= G`. Its *defect* is
`rho(Y) = chi(Y) - chi(G)`. The *relative defect* `rho(H,G)` is the minimum of `rho(Y)` over all
relative presentations.

**Theorem 1 (generalized Schanuel).** Let `Y` be any finite connected 2-complex with
`pi_1 Y ≅ G`. Then `pi_2(Y) ⊕ ZG^a ≅ ZG^(a + rho(Y))` for some `a`. Hence `rho(Y) >= 0`, and
`Y` is aspherical iff `rho(Y) = 0`.

**Theorem 2 (realization = efficiency).** The following are equivalent.
- (a) `RP(H,G)`.
- (b) Some finite 2-dimensional `K(G,1)` contains a finite `K(H,1)` subcomplex inducing `H`.
- (c) For every finite 2-dimensional `K(H,1)` `K`, some relative presentation `Y ⊇ K` has
  `rho(Y) = 0`.
- (d) `rho(H,G) = 0`.
- (e) `G ≅ <H, T | R>`, with `T` a finite set of new generators and `R` a finite set of
  relators, such that `|R| - |T| = chi(G) - chi(H)`.

The minimum over `Y ⊇ K` does not depend on the choice of `K`. Every `RP` pair is admissible,
meaning `pd_ZG I_{G/H} <= 1`.

**Theorem 2' (where admissibility sits).** Let `Y ⊇ K` be a relative presentation with no extra
vertices. Its relative cellular chains give an exact sequence of `ZG`-modules

`0 -> pi_2(Y) -> C_2(Y,K) -> C_1(Y,K) -> I_{G/H} -> 0`

with `C_1` and `C_2` free. The pair is admissible iff `pi_2(Y)` is a direct summand of `C_2(Y,K)`,
for one such `Y` or for all of them. Since Theorem 1 makes `pi_2(Y)` stably free of rank `rho(Y)`
for every `Y`, admissibility and every other stable-module invariant of `pi_2` carry no
information about `rho`. What separates admissible pairs from `RP` pairs is exactly the rank
count `rho(H,G) = 0`: a relative D(2)/efficiency problem.

**Theorem 3 (one-relator defect bound).** Let `G = <S | w>` with `w` cyclically reduced and not a
proper power, let `X` be its presentation complex, and let `H <= G` be finitely generated. Then
`H` is finitely presented by coherence. Let `C ⊂ X_H` be a finite core: a finite subcomplex of the
cover with `pi_1 C = H`. Then `C` is a finite `K(H,1)`, and with `n(C)` the number of its 2-cells,

`rho(H,G) <= max(n(C) - 1, 0)`.

So `RP(H,G)` holds whenever some core has at most one 2-cell. This is the w-disc case of
`two-cell-injective-maps-realize-relative-eg-pairs`.

**Calibration.** The bound is sharp. For `G = Z^2 = <a,b | [a,b]>` and `H` of index 2, the core is
the whole double cover (`n = 2`), so `rho <= 1`. `RP(H,G)` fails by an `H_2` count, so
`rho(H,G) = 1`. Free `H` and `H = G` give `rho = 0`.

**Consequence for the lane (strict reduction).** For torsion-free one-relator `G`, `REG_ω`
restricted to finitely generated pairs is equivalent to the following statement. For every
admissible finitely generated `H <= G`, `G` has a relative presentation `<H, T | R>` with
`|R| - |T| = 2 - |S| - chi(H)`. Equivalently, some core-based `Y_0` with `rho = n(C) - 1` can be
reduced by `n(C) - 1` in `chi`.

The literal w-disc class statement asks for more. It demands a witness inside the one fixed
presentation complex `X`, where a 2-cell-injective map forces `n(K) <= 1`. Theorem 2 allows any
`K(G,1)`.

**Negative computation note.** A 2-cell-injective core inside a finite cover `X̂ -> X` certifies
only `RP(H, π_1 X̂)`, for a finite-index subgroup of `G`. Descent runs `RP(H,G') => RP(H,G)` for
`G <= G'`, never upward. Upward fails already for `H = π_1 X̂` of finite index. So the proposed
cover search cannot certify `RP(H,G)` and was not run.
