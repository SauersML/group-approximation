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
3. **Ping-pong on the chambers at infinity: reduced to three building premises
   (2026-09-13).**
   - **Two ESTABLISHED lemmas.**
     - `opposition-ping-pong-criterion-gives-mixed-identity-freeness`: proximal
       elements whose poles are opposite to all their translates by finitely
       many constants force MIF.
     - `opposition-general-position-from-nowhere-domestic-dense-poles`: that
       general position follows from nowhere-dense domestic sets and dense pole
       pairs.
   - **Route.** `titz-witzel-kernel-mif-via-opposition-ping-pong` needs three
     OPEN premises:
     - `strongly-regular-building-elements-are-opposition-proximal`, i.e.
       uniform contraction. Caprace--Ciobotaru Prop. 2.10 gives it only
       pointwise.
     - `cocompact-building-lattices-have-dense-strongly-regular-poles`.
       Caprace--Ciobotaru Thm. 1.2 gives existence only.
     - `titz-witzel-kernel-elements-are-nowhere-domestic-at-infinity`, the crux.
       Collineations of quadrangles fixing an ovoid or spread map no chamber to
       an opposite one (Neyt--Parkinson--Van Maldeghem), so this must use the
       lattice.
   - **Rank-one methods are out.** Every geodesic line of `X` lies in an
     apartment, so no isometry is rank one. That rules out Rybak's curtain-model
     route.
