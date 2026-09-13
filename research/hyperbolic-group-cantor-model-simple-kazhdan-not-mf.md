---
rg: 2
id: hyperbolic-group-cantor-model-simple-kazhdan-not-mf
kind: claim
title: Every non-elementary hyperbolic group with trivial finite radical has a minimal topologically free Cantor action with a finite generating clopen family and a north–south element
distinct_from:
  free-product-finite-groups-boundary-simple-kazhdan-not-mf: that covers virtually free groups with trivial edge stabilizers, whose boundary is already Cantor; this asks for a zero-dimensional model for every non-elementary hyperbolic group, including one-ended ones whose Gromov boundary is connected.
---

**OPEN.** Let `Γ` be a non-elementary hyperbolic group with no nontrivial finite normal subgroup. The claim is that
`Γ` acts on a Cantor space `X` minimally and topologically freely, with a finite family of clopens whose translates
separate points (H-gen), and with some element north–south.

If so, `paradoxical-cantor-actions-give-simple-kazhdan-not-mf` and
`north-south-minimal-cantor-action-is-paradoxical` make `EL_N(LC(X, F_q) ⋊ Γ)/Z` (`N >= 3`) an infinite finitely
generated simple Kazhdan group with no nontrivial MF quotient, for every such `Γ`. That would include surface groups
and hyperbolic Kazhdan groups.

## Attempts

- **Gromov boundary.**
  - For one-ended `Γ`, `∂Γ` is connected (recalled, not imported), so `LC(∂Γ, k) = k` and the crossed product
    degenerates to the group algebra.
  - `∂Γ` is a Cantor space exactly in the virtually free case (recalled). That case needs only trivial edge
    stabilizers or another direct argument, as in the free-product family.
  - This route dies for one-ended groups.
- **Horofunction boundary.** For hyperbolic groups the horofunction boundary is compact and totally disconnected, and
  maps finite-to-one onto `∂Γ` (recalled, Webster–Winchester; not read).
  - Loxodromic elements should still act north–south on the fibres over their fixed points.
  - Unverified: minimality (the boundary may contain proper closed invariant subsets); topological freeness; (H-gen)
    (Busemann cocycles take finitely many local patterns, which suggests a generating family).
  - Gate: read Webster–Winchester and Coornaert–Papadopoulos verbatim before anything more.
- **Symbolic coding.** Coornaert–Papadopoulos code `∂Γ` as a factor of a subshift of finite type. The coding space is
  not a `Γ`-space, so it does not directly give a Cantor `Γ`-action.
- **Cheap substitute.** A free subgroup `F_2 ≤ Γ` on `∂F_2` gives groups over `LC(∂F_2) ⋊ F_2`, which do not involve
  `Γ`. Inducing the action to `Γ` needs finite index.
- **Symbolic model instead of a boundary (un-horofunction-families, 2026-09-13; unreviewed).** The downstream conclusion
  no longer needs this claim.
  - `f2-groups-have-paradoxical-free-minimal-subshifts` gives every finitely generated `Γ ⊇ F_2` a free minimal Cantor
    subshift with (H-gen) and a two-piece paradox. The construction: encode a paradoxical decomposition of `Γ`, multiply
    by a Gao–Jackson–Seward free minimal subflow, and take a minimal subset.
  - `f2-group-subshift-elementary-simple-kazhdan-not-mf` then gives an infinite finitely generated simple Kazhdan
    `EL_N(LC(Z, F_q) ⋊ Γ)/Z` with no nontrivial MF quotient.
  - Non-elementary hyperbolic groups contain `F_2` (Gromov; recalled, not imported). So every such `Γ`, one-ended
    included, gets such a group, with no trivial-finite-radical hypothesis, since freeness comes from the subflow.
  - What stays open here is only the natural-boundary form: a boundary-type model with a north–south element.
- **Horofunction boundary, (H-gen) part (elementary).** The horofunction compactification lies in `∏_g {−|g|,…,|g|}`.
  With `(γ·h)(g) = h(γ^{-1}g) − h(γ^{-1})`, the increments `h(gs) − h(g) = (g^{-1}·h)(s)` show that translates of the
  clopens `{h : h(s) = v}` (`s ∈ S`, `v ∈ {−1,0,1}`) separate points. Minimality, topological freeness and north–south
  dynamics are still unchecked. Webster–Winchester and Coornaert–Papadopoulos were not read. Details are in
  `research/artifacts/un-horofunction-families-paradoxical-subshifts-2026-09-13.md` §8.
