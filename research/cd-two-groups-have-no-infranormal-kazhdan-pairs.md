---
rg: 2
id: cd-two-groups-have-no-infranormal-kazhdan-pairs
kind: claim
title: A torsion-free group of cohomological dimension two contains no Kazhdan subgroup strictly compressed by conjugation
distinct_from:
  kun-thom-double-of-hyperbolic-pair-has-finite-cd: that shows infranormal non-normal Kazhdan pairs, and hence nonsofic Kun--Thom doubles, occur in some finite cohomological dimension; this asks whether dimension two excludes them.
  arithmetic-integral-subgroup-is-incompressible: that excludes strict compression of SL_n(Z) inside GL_n(Q) through covolume; this asks for exclusion of strict compression of every Kazhdan subgroup in dimension two, where no covolume is available.
  vcd-two-groups-contain-no-kazhdan-commuting-pairs: that excludes commuting partners of infinite Kazhdan subgroups in dimension two; this is the remaining compression configuration, with no commuting partner.
---

**OPEN.** Let `K` be torsion-free with `cd K <= 2`, let `Gamma <= K` be a nontrivial Kazhdan subgroup, and let
`t in K` satisfy `t Gamma t^-1 <= Gamma`. The claim is that then `t Gamma t^-1 = Gamma`.

**Consequence.** No subgroup of `K` is an infranormal non-normal Kazhdan pair. By
`infranormal-nonnormal-has-infinite-compression-orbit`, a non-normal pair needs a strict
compressor. So neither Kun--Thom Theorem A conclusion can be realized inside `K`:
- the double (`kt-pair-group-double-is-nonsofic`);
- the wreath product, which is already excluded by `vcd-two-groups-contain-no-kazhdan-commuting-pairs`
  (CD3).

Together with the compression and lamp fences, every recorded nonsoficity certificate would then
be vacuous in the Titz Mite--Witzel kernels and in Radu's lattice.

## Attempts

- **The ascending HNN extension (proved, 2026-09-13).** Suppose `t Gamma t^-1 < Gamma` strictly,
  and put `H = <Gamma, t>`, `Gamma_k = t^-k Gamma t^k`, `Gamma_inf = union_k Gamma_k`.
  - `Gamma_inf` is normal in `H`, and `H = Gamma_inf <t>`.
  - If `t^m` lay in `Gamma_inf` for some `m >= 1`, then `t^m` would lie in `Gamma`, and
    `t^m Gamma t^-m = Gamma` would contradict the strict descending chain. So `<t>` meets
    `Gamma_inf` trivially.
  - The direct limit of `Gamma --phi--> Gamma --phi--> ...`, with `phi = c_t`, maps isomorphically
    onto `Gamma_inf`.

  Hence `H ~= Gamma *_phi`, the ascending HNN extension, and the claim is equivalent to
  `cd(Gamma *_phi) >= 3` for every Kazhdan subgroup and strict compressor in dimension two.
- **A cohomological necessary condition (proved).** Let `cd K <= 2`, `Gamma` Kazhdan (so
  `cd Gamma = 2`), and `t` a strict compressor. Let `M = Z[<t>] (x) A`, for an abelian group `A`,
  with `Gamma_inf` acting trivially and `t` shifting.
  - The HNN Mayer--Vietoris sequence gives `H^3(H;M) = coker(1 - psi)` on `H^2(Gamma;M)`.
  - The sum map `M -> A` is surjective on `H^2(Gamma; -)`, because `H^2` is right exact in top
    degree. It intertwines `psi` with `phi^*`.
  - So `cd H <= 2` forces `1 - phi^*` to be surjective on `H^2(Gamma;A)` for every `A`.
  - Over `Q` this says `1 - phi_*` is injective on `H_2(Gamma;Q)`.
  - If `H_2(Gamma;Q)` is finite-dimensional, then `1 - phi_*` is bijective. Corestriction
    `c : H_2(Gamma;Q) -> H_2(K;Q)` satisfies `c phi_* = c`, since `c_t` is inner in `K`. So `c = 0`.

  A strict compression in dimension two with finite-dimensional `H_2(Gamma;Q)` must therefore kill
  every rational 2-class of `Gamma` in `K`.
- **Convex-cocompact case (sketch, not written as a proof).** Suppose `K` acts properly and
  cocompactly on a CAT(0) space with no Euclidean factor, and `Gamma` acts cocompactly on a unique
  minimal convex set `C`.
  - Then `t C = C`, so `t` lies in the stabilizer `S` of `C`, and `Gamma` has finite index in `S`.
  - Conjugation by `t` preserves `[S : Gamma]`, so `t Gamma t^-1 = Gamma`.
  - Uniqueness of `C` and the no-Euclidean-factor hypothesis were not checked for the Titz--Witzel
    buildings.
- **Where it stops.** Nothing forces a Kazhdan subgroup of `K` to be convex-cocompact, or its
  rational 2-classes to survive in `K`. The finite-dimension example of
  `kun-thom-double-of-hyperbolic-pair-has-finite-cd` has a non-quasiconvex `Gamma_hat` inside a
  hyperbolic group of dimension greater than two.
