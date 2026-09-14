---
rg: 2
id: subshift-elementary-group-reduced-cstar-is-not-mf
kind: claim
title: For an infinite minimal subshift X, the reduced C-star algebra of EL_3(LC(X,F_q)⋊Z) is not MF
distinct_from:
  directly-finite-subshift-el-n-reduced-cstar-is-mf: that is the positive question for EL_n, n ≥ 4, over directly finite subshift rings; this is the negative side at the note's group, with a conditional route through the Laurent lattice inside it.
  sl4z-reduced-cstar-is-not-mf: that is the negative question for SL_4(Z) in characteristic zero; this is the positive-characteristic simple Kazhdan LEF group, which contains every SL_n(F_q[t^±1]).
---

**OPEN.** Let `X` be an infinite minimal subshift, `q` a prime power and `G_X = EL_3(LC(X,F_q)⋊_T Z)`. Then
`C*_r(G_X)` admits no injective *-homomorphism into a norm matrix corona `∏_n M_{k_n} / ⊕_n M_{k_n}`.

Conditional route: `subshift-el-reduced-not-mf-from-laurent-sl4-stability`, which requires the open
`laurent-sl4-matricially-stable`.

## Attempts

- **Through stability of the Laurent lattice.** Live and conditional (route above). By
  `laurent-sl4-stability-makes-overgroups-reduced-non-mf` the claim follows from point-norm matricial stability of
  `SL_4(F_q[t,t^{-1}])` alone, not of `G_X`.
- **Genuine representations of `G_X`.** Void: `G_X` has no nontrivial finite-dimensional unitary representation
  (`minimally-almost-periodic-groups-are-not-pmf`), so every MF embedding uses non-genuine asymptotic representations.
- **The note's finite models.** Every representation of the periodic-word models fails to converge strongly
  (`periodic-word-model-representations-never-converge-strongly`), so an MF embedding cannot come from them.
- **What a counterexample needs.** An MF embedding restricts to asymptotic homomorphisms of `SL_4(F_q[t^{±1}])` that
  are far from every genuine representation on the block `SL_2`, since genuine ones all have block-`SL_2` norm 4
  (`laurent-sl-n-representations-have-sl2-invariant-vectors`).
- **A weaker crux than stability (sk-mf-laurent, 2026-09-14).**
  - Route `subshift-el-reduced-not-mf-from-laurent-corona-norm-four` needs only
    `laurent-sl4-corona-representations-have-block-sl2-norm-four`: every corona representation of `Λ` gives
    block-`SL_2` norm 4. Stability implies it (`laurent-corona-norm-four-from-matricial-stability`).
  - By `laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum` (unreviewed) the crux holds off the full-spectrum
    case.
  - What remains is exactly the Haar-spectrum case, which contains every MF embedding. This is the positive-characteristic
    form of the `SL_4(Z)` wall.
