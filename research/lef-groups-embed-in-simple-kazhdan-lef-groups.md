---
rg: 2
id: lef-groups-embed-in-simple-kazhdan-lef-groups
kind: claim
title: Every finitely generated LEF group is a subgroup of an infinite finitely generated simple Kazhdan LEF group
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that is the residually finite case, proved; this is the LEF case, open, which would make LEF exactly the class of finitely generated subgroups of infinite simple Kazhdan LEF groups.
---

**OPEN.** Does every finitely generated LEF group embed in an infinite, finitely generated, simple group with property
(T) that is LEF? Subgroups of LEF groups are LEF, so a yes means LEF is exactly the class of finitely generated
subgroups of such groups. Kionke–Schesler's no-(T) theorem (arXiv:2304.09307, Theorem 1.2) also takes residually
finite input.

## Attempts

- **Overgroup (done).** `rf-groups-lie-in-derived-subgroups-of-rf-groups` part 2 gives `Γ ≤ [Δ,Δ]` with `Δ` f.g. LEF,
  so Whitehead's lemma reduces the question to one missing input. That input is a f.g. LEF group `Δ ⊇ Γ` with a free
  (or topologically free) minimal subshift `X` such that `LC(X,F_2) ⋊ Δ` embeds in an algebraic matrix ultraproduct
  over `F_2`.
- **Toeplitz levels (dies).** Levels are finite-index normal subgroups of the acting group, and freeness from levels
  needs trivial intersection. That forces the acting group, hence `Γ`, to be residually finite.
- **Genuine finite models (dies).** Kerr–Nowak RF models of a free action separate each finite set of group elements,
  which again forces a residually finite acting group. sk-general-actions-a landed this as
  `free-subshift-with-finite-models-forces-rf-group`.
- **Ultralimit subshifts along partial models (incomplete).** Take LEF models `(Q_n, φ_n)` of `Δ`, colorings
  `c_n : Q_n -> A`, and the subshift whose `W`-patterns are those occurring in `(Q_n,c_n)` for `ω`-most `n`.
  - Exact window models are automatic: each window has finitely many patterns. So the crossed product embeds in
    `∏_ω M_(|Q_n|)(F_2)`.
  - What is missing is minimality and freeness with bounds uniform in `n`.
  - Internal levels of bounded index give genuine finite quotients of `Δ`, which forces RF.
  - Internal levels of unbounded index destroy uniform syndeticity.
  - Random colorings give the full shift.
- **Possible ways around.**
  - Topological freeness plus `steinberg-elementary-groups-are-simple-mod-centre`, which needs free points only on a
    dense set.
  - Simple LEF rings with local matrix units containing `F_2[Δ]` that are not crossed products.

**Review (sk-verify-3, 2026-09-13): route PASS.** `lef-groups-embed-in-simple-kazhdan-lef-groups-proof` re-derived (overgroup `Δ × Z`, `[Δ,Δ] ≤ [L,L] ↪ EL_3`). With both requires established the claim is established, so the OPEN display and pre-route Attempts need restating by the owner. See `research/artifacts/sk-review-3-2026-09-13-part6.md` §A3.
