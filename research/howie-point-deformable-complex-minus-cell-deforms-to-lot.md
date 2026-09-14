---
rg: 2
id: howie-point-deformable-complex-minus-cell-deforms-to-lot
kind: claim
title: If a 2-complex 3-deforms to a point, then deleting any one 2-cell leaves a complex that 3-deforms to a LOT complex (Howie 1983)
distinct_from:
  contractible-2-complex-minus-a-cell-is-aspherical: that asserts asphericity of every one-cell complement of a finite contractible 2-complex; this only moves such a complement into the LOT class by 3-deformations when the whole complex 3-deforms to a point, and asserts no asphericity.
  lot-complexes-with-vanishing-first-l2-betti-are-aspherical: that proves asphericity of LOT complexes whose group has vanishing first L2-Betti number; this reduces one-cell complements of point-deformable complexes to LOT complexes.
  stable-andrews-curtis-conjecture: that is the conjecture that balanced presentations of the trivial group are stably AC-trivial, whose presentation complexes then 3-deform to a point; this is a theorem about what such a deformation does to one-cell complements.
artifacts:
  - research/artifacts/ideas-bridges-2-2026-09-14.md
---

**ESTABLISHED** by literature import `howie-3-deformation-lot-citation`.
Pinned verbatim from two secondary sources. The primary paper was not read at
source (see the citation route).

**Statement.** Let `L` be a 2-complex that 3-deforms to a point, and let `e` be a
2-cell of `L`. Then the subcomplex `L - e` 3-deforms to a LOT complex: the
presentation complex of a labelled oriented tree, as in
`lot-complexes-with-vanishing-first-l2-betti-are-aspherical`.

**Consequences recorded in the sources.**
- If every finite contractible 2-complex 3-deforms to a point, asphericity of all
  LOT complexes implies the compact case of Whitehead's conjecture (Cerdeiro).
- Howie (1985), as quoted there: LOT complexes are spines of ribbon disc
  complements, and asphericity of ribbon disc complements is equivalent to
  asphericity of LOT complexes.
- Used by `balanced-kervaire-stable-ac-lot-proof`. Under stable Andrews--Curtis,
  a balanced Kervaire killing failure becomes a LOT group with torsion.
