---
rg: 2
id: laurent-sl4-stability-makes-overgroups-reduced-non-mf
kind: claim
title: If SL_4(F_q[t^±1]) is point-norm matricially stable, no countable group containing it, G_X included, has MF reduced C-star algebra
distinct_from:
  matricially-stable-overgroups-of-sl4z-are-not-reduced-mf: that assumes stability of the overgroup and uses the published Magee-de la Salle theorem for SL_4(Z); this assumes stability of the Laurent lattice alone, restricts the MF embedding to it first, and uses the congruence invariant vectors of the Laurent lattice.
  periodic-word-model-representations-never-converge-strongly: that excludes every representation of the note's finite models; this excludes every MF embedding of the reduced algebra once the Laurent lattice is stable, whatever asymptotic representations realize it.
artifacts:
  - research/artifacts/sk-matricial-stability-laurent-sl4-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `q` be a prime power, `A = F_q[t,t^{-1}]` and `Λ = SL_4(A)`. Suppose `Λ` is
point-norm matricially stable in Dadarlat's sense (`dadarlat-matricial-stability-obstruction`, §1): every
operator-norm asymptotic homomorphism `φ_n : Λ → U(k_n)` admits homomorphisms `π_n : Λ → U(k_n)` with
`‖φ_n(g) − π_n(g)‖ → 0` for each `g`. Then `C*_r(Γ)` is not MF for every countable group `Γ` containing a copy of `Λ`.

**Dichotomy form.** If `C*_r(Γ)` is MF for one countable `Γ ⊇ Λ`, then `Λ` is not matricially stable.

**Instances.**
- `G_X = EL_3(LC(X,F_q)⋊Z)` for every infinite minimal subshift `X`: `SL_6(A) ≤ G_X`
  (`subshift-elementary-groups-contain-laurent-sl-n-lattices`, k = 2), and `Λ` is its upper-left block.
- `EL_n(R)` for `n ≥ 4` and every ring `R` containing `A` as a unital subring, since `SL_4(A) = EL_4(A) ≤ EL_4(R)`.

**Why stability of `Λ` alone suffices.** An MF embedding of `C*_r(Γ)` restricts to an MF embedding of `C*_r(Λ)`,
because `λ_Γ|_Λ` is a multiple of `λ_Λ`. The same restriction sharpens the `SL_4(Z)` node: stability of `SL_4(Z)`
itself would make `C*_r(Γ)` non-MF for every `Γ ⊇ SL_4(Z)`.

Proof: route `laurent-sl4-stability-makes-overgroups-reduced-non-mf-proof`.
