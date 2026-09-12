---
rg: 2
id: iwahori-outlier-localization
kind: route
title: Iwahori central-regular outlier localization
artifacts:
  - notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md
target: iwahori-outlier-repair
requires:
  - central-regular-edge-constituents-are-fell-pure
  - edge-pair-mixed-gap-collapse
---

The mixed edge character converges to the regular character of
`B/⟨z⟩ ≅ ℤ * C₂`; Kesten's gap makes every fixed low-energy spectral window
`o(d_n²)`-dimensional, and the almost-invariant identity concentrates
there. The low-energy projection commutes with both edge commutants, hence
is a bimodule decomposing into low-energy `Hom(θⱼ, πᵢ)` blocks tensored
with full multiplicity rectangles. With the dimension-tight theorem this
reduces the outlier-repair endpoint iwahori-outlier-repair to mixed-gap collapse for
high-dimensional edge-irreducible pairs, edge-pair-mixed-gap-collapse — arbitrary sparse operator
subspaces are out of the gate.

The extreme-trace purification theorem
`central-regular-edge-constituents-are-fell-pure` sharpens the surviving
pairs: after deleting `o(1)` overlap mass, both edge irreducibles may be
required individually to have dimensions tending to infinity and normalized
characters converging pointwise to the regular character of
`B/<z> ~= Z*C_2`.  This removes cancellation among nonregular constituent
characters as a source of the outlier.  It does not remove a sparse
low-energy line represented by a full-rank near-intertwiner, which remains
the content of `edge-pair-mixed-gap-collapse`.
