---
rg: 2
id: farey-fock-representation-of-t-is-not-bekka-amenable
kind: claim
title: "The Farey–Fock representation M of Thompson's T is not Bekka-amenable (δ_* > 0): off the vacuum, Ad M restricted to PSL_2(Z) is tempered and has a spectral gap, so almost invariant densities concentrate on the vacuum, and only Möbius maps fix the vacuum ray; hence every Weyl-twisted V ⊗ M̄ family has no almost invariant vectors"
distinct_from:
  lifted-thompson-t-farey-fock-twist-bound: that builds M, proves the twist bound and the dichotomy on δ_*, and leaves (Q1) open; this answers (Q1) with NO
  lifted-thompson-t-euler-class-in-kahler-subspace: that is (K), an exact invariant unitary structure; this kills one approximate lead toward it and does not decide (K)
  bekka-valette-amenable-t-dichotomy: that collapses amenable representations of Kazhdan groups; T is not Kazhdan-type here, and the gap comes from the lattice PSL_2(Z) inside T
artifacts: []
---

**ESTABLISHED** by `farey-fock-representation-of-t-is-not-bekka-amenable-proof`, modulo classical
imports recalled with references in that proof (the same Shale/Fock imports as
`lifted-thompson-t-farey-fock-twist-bound`, plus standard facts on the weight-2 holomorphic
discrete series, Fell absorption, restriction to lattices, and Hulanicki–Kesten).

## Notation

As in `lifted-thompson-t-farey-fock-twist-bound`: `T = PPSL_2(Z)` on the circle, `H`, `J_0`, the
Fock space `F`, the projective representation `M` with `M(g)W(f)M(g)^* = W(g·f)`, the Bekka defect
`δ(ρ) = max_{s∈S} ‖M(s)ρM(s)^* − ρ‖_1` and `δ_* = inf_ρ δ(ρ)`. The circle is identified with
`|z| = 1` so that `PSL_2(R)` acts through `PSU(1,1)`, as in that node.

## Statement

- **(1) Vacuum concentration.** Let `Γ = PSL_2(Z) ≤ T` and `S_Γ` a finite generating set. There is
  `κ > 0` such that for every unit `ξ ∈ HS(F)`:
  `min_{|c|=1} ‖ξ − c P_Ω‖_2 ≤ 2κ^{-1} max_{s∈S_Γ} ‖M(s)ξM(s)^* − ξ‖_2`, with `P_Ω = |Ω⟩⟨Ω|`.
- **(2) Vacuum rigidity.** If `M(g)Ω ∈ CΩ` then `g` is a single Möbius map, i.e. `g ∈ Γ`.
- **(3) Main claim.** `δ_* > 0`. More precisely, for any `g_0 ∈ T ∖ Γ` there is `ε > 0` with
  `max_{s ∈ S_Γ ∪ {g_0}} ‖M(s)ρM(s)^* − ρ‖_1 ≥ ε` for every density `ρ` on `F`.

## Consequences (class kill)

- (Q1) of `lifted-thompson-t-farey-fock-twist-bound` is answered NO.
- By (3c) of that node, every Weyl-twisted representation `W(√t b)M ⊗ M̄` of `T̄`, and every
  `V ⊗ M̄` whose multiplier matches, has all unit vectors at defect `≥ δ_*/2`, uniformly in `t`.
  So none of them bounds the twist cost `c`.
  - Invariant: the Bekka defect `δ_*`. It is bounded below by the spectral gap of the lattice
    `PSL_2(Z)` on the non-vacuum (tempered) part of `HS(F)`, together with one non-Möbius element.
  - Step where every member dies: the density matrix `ξ^*ξ` of an almost invariant vector (step
    (2) of the target) is almost invariant, so it is close to `P_Ω`, and `P_Ω` is not `T`-invariant.
- Route (3a) of that node never fires. The profile `A(η)` of (3b) is `+∞` for `η < δ_*`, so (3b)
  never fires either. The metaplectic lead of `lifted-thompson-t-euler-class-in-kahler-subspace`
  (the w13 spark) is dead in this model.
- This answers the "Not claimed" item of the target: the non-amenable `Λ = PSL_2(Z)` works, with
  the vacuum piece handled separately by (2).

## Not claimed

- Nothing about (K) itself, relative (T) of the centre of `T̄`, or Haagerup for `T̄`.
- Nothing about Fock representations over other complex structures `J ≠ J_0`, or over other
  circle models of `T` (for example a smoothing in which no copy of `PSL_2(Z)` acts isometrically
  on a tempered one-particle space). Such models escape (1) only if no non-amenable subgroup acts
  with a tempered one-particle representation; this is the precise gap left open.
