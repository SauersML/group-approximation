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
out.  Amenable implies MF lies outside what this repository establishes and
does not follow from anything in it; it is the manuscript's citation to
Tikuisis--White--Winter. -/
theorem isAmenable_subgroup_CliffordBS (H : Subgroup CliffordBS) :
    IsAmenable H :=
  IsAmenable.subgroup
    (isAmenable_of_hasInvariantMean hasInvariantMean_CliffordBS) H

/-- The realized quotient, cut out by any set of elements, is amenable. -/
theorem isAmenable_closure_CliffordBS (S : Set CliffordBS) :
    IsAmenable (Subgroup.closure S) :=
  isAmenable_subgroup_CliffordBS _

/-! ## The remaining literature input, made explicit

The manuscript's sentence concludes "hence MF", and that step is
Tikuisis--White--Winter.  It is not proved here and cannot be: the theorem
is formalized in no proof assistant.  Rather than leave it as prose, it is
recorded as an explicit hypothesis with no inhabitant postulated --- the
same discipline `Computability.MarkovMFConsequences` applies to the
Adian--Rabin construction.  A reader can then see exactly what the
manuscript's sharpness paragraph rests on: this structure, and nothing
else. -/

/-- The Tikuisis--White--Winter input: every countable amenable group is
operator-MF.  **No inhabitant of this structure is constructed anywhere in
this repository**, and none can be without formalizing that theorem. -/
structure AmenableImpliesMF : Prop where
  /-- Amenable countable groups are operator-MF. -/
  mf : ∀ (G : Type) [Group G] [Countable G], IsAmenable G → IsOperatorMF G

/-- **The manuscript's sharpness conclusion, as a conditional theorem.**
Every subgroup of the Clifford--`BS(1,2)` extension is MF, given
Tikuisis--White--Winter and nothing further.  The amenability half is
fully machine-checked above; this states precisely where the citation
enters. -/
theorem isOperatorMF_subgroup_CliffordBS (tww : AmenableImpliesMF)
    (H : Subgroup CliffordBS) [Countable H] : IsOperatorMF H :=
  tww.mf _ (isAmenable_subgroup_CliffordBS H)

/-- The realized quotient of Theorem C is MF, given Tikuisis--White--Winter. -/
theorem isOperatorMF_closure_CliffordBS (tww : AmenableImpliesMF)
    (S : Set CliffordBS) [Countable (Subgroup.closure S)] :
    IsOperatorMF (Subgroup.closure S) :=
  isOperatorMF_subgroup_CliffordBS tww _

end CyclicBaseCalibration
end GroupApproximation
