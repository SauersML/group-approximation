---
rg: 2
id: zariski-dense-psl-subgroups-are-completely-selfless
kind: claim
title: Zariski-dense subgroups of PSL(d,R) have completely selfless reduced C*-algebras (Ozawa, Proposition 16 with Theorem 14)
distinct_from:
  ozawa-php-groups-completely-selfless: that imports Ozawa's Theorem 14 with Proposition 15 (extreme boundaries, acylindrically hyperbolic groups); this imports Proposition 16, the Zariski-dense linear instance of the same property.
  vigdorovich-linear-selflessness: that proves selflessness for nontrivial linear groups with trivial amenable radical; this is the earlier, narrower PSL(d,R) instance, whose hypothesis is only Zariski density.
---

**ESTABLISHED (literature)** by `zariski-dense-psl-subgroups-are-completely-selfless-citation`.

Let `d >= 2` and let `Γ <= PSL(d,R)` be Zariski-dense. Then `Γ` has Ozawa's property
`P_PHP`, so `(C*_r(Γ), τ)` is completely selfless, hence selfless.

**Instance: torsion-free finite-index subgroups of `SL_3(Z)`** (for example `Γ(3)`). Here
`PSL(3,R) = SL(3,R)`, since a real scalar `ωI` with `ω^3 = 1` is `I`. A finite-index
`Γ <= SL_3(Z)` is Zariski-dense in `SL_3(R)`, by an elementary argument:
- for each `i != j`, `Γ` meets the root group `U_ij(Z) = {I + n E_ij}` in a finite-index
  subgroup, which is infinite;
- an infinite subset of the line `U_ij(R) ≅ R` is Zariski-dense in it, so the Zariski closure
  of `Γ` contains every `U_ij(R)`;
- the Zariski closure of a subgroup is a subgroup, and the `U_ij(R)` generate `SL_3(R)`.
