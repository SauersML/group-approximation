---
rg: 2
id: titz-witzel-kernels-are-mif
kind: claim
title: The simple finite-index kernels of the Titz Mite--Witzel C2-tilde lattices are MIF
distinct_from:
  fp-simple-kac-moody-lattices-are-mif: that is the MIF theorem for simple Kac--Moody lattices, which act on twin buildings; this asks the same property for the simple kernels of uniform lattices on exotic C2-tilde buildings.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: that imports existence, simplicity and property (T) of these kernels; this asks whether they satisfy no mixed identity.
artifacts:
  - research/artifacts/solve-bh-cat0-automatic-2026-09-13.md
---

**OPEN.** Let `Γ̌ = Γ̌_i^q` be one of the five simple groups of
`titz-witzel-simple-kazhdan-cat0-lattices-exist`. The claim is that `Γ̌` is MIF:
for every nontrivial `w ∈ Γ̌ * <x>` there is `g ∈ Γ̌` with `w(g) ≠ 1`.

**Why it matters.** With `titz-witzel-lattices-pbh-from-mif-kernels`, this
places the lattices `Γ_i^q`, and every subgroup of them, in the permutational
Boone--Higman class.

## Attempts

1. **Rybak's Kac--Moody method, unclear.** According to the lane report of
   2026-09-13 recorded on `fp-simple-kac-moody-lattices-are-highly-transitive`,
   that proof runs through a general-type action on a hyperbolic space that is
   topologically free on its limit set. `Γ̌` acts on a Euclidean building, which
   has no rank-one isometries. Whether `Γ̌` has some other action of this kind
   isn't known here.
2. **Mixed identities from micro-supported actions, not applicable.** No
   micro-supported action of `Γ̌` on a Hausdorff space is known. The natural
   boundary action is on the chamber space at infinity of the building.
