import GroupApproximation.Algebra.AmenableRat
import GroupApproximation.Monsters.CyclicBaseCalibration
import GroupApproximation.Monsters.CliffordLampLocallyFinite

/-!
# The Clifford--`BS(1,2)` extension is amenable

The manuscript's sharpness paragraph reads: the affine group
`BS(1,2) ≅ ℤ[1/2] ⋊ ℤ` is solvable, the Clifford lamp group on its coset
space is locally finite, so their semidirect product is amenable; the
realized quotient is a subgroup of that amenable group and is therefore
amenable, hence MF by Tikuisis--White--Winter.

Every step of that except the last is proved here, on the repository's own
objects rather than on a paraphrase of them.  `BSLike` and `CliffordBS`
are literally `SemidirectProduct`s, so the semidirect-product theorem
applies directly:

* `Multiplicative ℚ` is amenable (a directed union of cyclic groups), and
  the manuscript's `ℤ[1/2]` sits inside it --- the repository models the
  translation part by all of `ℚ`, which only makes the ambient group
  bigger and the amenability statement stronger;
* `Multiplicative ℤ` is amenable, so `BSLike` is;
* the lamp group is locally finite, hence amenable, so `CliffordBS` is;
* amenability passes to subgroups, so *every* subgroup of `CliffordBS` is
  amenable --- in particular the realized quotient, however its generating
  set is chosen.

What is **not** here, and cannot be: amenable implies MF.  That is
Tikuisis--White--Winter, it is formalized in no proof assistant, and it
remains the single external input of the manuscript sentence.
-/

namespace GroupApproximation
namespace CyclicBaseCalibration

open Amenability

/-- `BSLike`, the repository's affine model, is amenable. -/
theorem hasInvariantMean_BSLike : HasInvariantMean BSLike :=
  hasInvariantMean_semidirectProduct hasInvariantMean_rat hasInvariantMean_int

/-- The Clifford lamp group on the coset space is amenable, being locally
finite. -/
theorem hasInvariantMean_lampGroup :
    HasInvariantMean (CliffordAlgebraLamp.lampGroup Sites) :=
  hasInvariantMean_of_isLocallyFiniteGroup
    (CliffordAlgebraLamp.isLocallyFiniteGroup_lampGroup Sites)

/-- **The Clifford--`BS(1,2)` extension is amenable.** -/
theorem hasInvariantMean_CliffordBS : HasInvariantMean CliffordBS :=
  hasInvariantMean_semidirectProduct hasInvariantMean_lampGroup
    hasInvariantMean_BSLike

/-- **Every subgroup of the extension is amenable** --- in particular the
realized quotient of Theorem C, whatever generating set is used to cut it
out.  Amenable implies MF is not proved here and is not provable from
anything in this repository; it is the manuscript's citation to
Tikuisis--White--Winter. -/
theorem isAmenable_subgroup_CliffordBS (H : Subgroup CliffordBS) :
    IsAmenable H :=
  IsAmenable.subgroup
    (isAmenable_of_hasInvariantMean hasInvariantMean_CliffordBS) H

/-- The realized quotient, cut out by any set of elements, is amenable. -/
theorem isAmenable_closure_CliffordBS (S : Set CliffordBS) :
    IsAmenable (Subgroup.closure S) :=
  isAmenable_subgroup_CliffordBS _

end CyclicBaseCalibration
end GroupApproximation
