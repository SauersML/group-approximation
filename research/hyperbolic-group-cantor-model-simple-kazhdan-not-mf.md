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
