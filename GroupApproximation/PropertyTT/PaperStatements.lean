import GroupApproximation.PropertyTT.BoundedGeneration
import GroupApproximation.PropertyTT.FiniteTypeLeavittTT
import GroupApproximation.PropertyTT.LeavittAllRanksTT
import GroupApproximation.PropertyTT.RankFourRelativeTT

/-!
# Paper statements for strong-division rings and `(TT)/T`

This file is the rigidity paper's public theorem surface.  Each declaration is
intended to correspond verbatim to one numbered theorem in the manuscript.
It contains no nonsoficity input; the combined nonsofic corollary belongs in a
separate endpoint so that the rigidity theorem has an independent dependency
closure.
-/

namespace GroupApproximation
namespace PropertyTTPaper

noncomputable section

/-- **Strong relative root theorem.**  Over the free associative `ZMod 2`
algebra, every Hilbert-space quasi-cocycle is bounded on the `(0, 3)`
elementary root subgroup.  No hypothesis excluding invariant vectors is used.

This is deliberately stated as `HasRelativeTT`, rather than merely relative
`(TT)/T`, so that the public theorem records the stronger conclusion proved by
the rank-four argument. -/
theorem freeCharacteristicTwo_root_hasRelativeTT
    (X : Type) [Fintype X] :
    HasRelativeTT.{0, 0}
      (elementaryGroup (Fin 4) (FreeAlgebra (ZMod 2) X))
      (elementaryRootSubgroup (0 : Fin 4) 3 (by decide)) :=
  RankFourRelativeTT.hasRelativeTT_X03 X

/-- **Coordinate-block factorization.**  If every nonzero element of `R`
admits a single sandwich to `1`, then every invertible `n × n` matrix is a
product of at most `2*n+6` factors, each either an elementary transvection or
an element of the fixed coordinate block omitting `j`.

This is not a claim of bounded elementary generation: one coordinate copy of
`GL_(n-1)(R)` is part of the generating set. -/
theorem coordinateBlock_factorization
    (R : Type*) [Ring R] [Nontrivial R]
    (n : ℕ) (hn : 2 ≤ n)
    (hdiv : HasSingleSandwichDivision R) (j : Fin n) :
    IsBoundedProduct (Matrix (Fin n) (Fin n) R)ˣ
      (coordinateBlockOrRoot j) (2 * n + 6) := by
  letI : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [Fintype.card_fin]
      exact hn)
  simpa using
    (boundedProduct_coordinateBlockOrRoot (R := R) hdiv j)

/-- **Four-hypothesis synthesis theorem.**  A finite free characteristic-two
presentation, binary Leavitt self-similarity, single-sandwich division, and
trivial elementary diagonal class together imply `(TT)/T` in every
elementary rank at least three. -/
theorem finitePresentation_elementaryGroup_hasTTmodT
    (R : Type) [Ring R] [Nontrivial R]
    (X : Type) [Fintype X]
    (f : FreeAlgebra (ZMod 2) X →+* R)
    (hf : Function.Surjective f)
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R)
    (n : ℕ) (hn : 3 ≤ n) :
    HasTTmodT.{0, 0} (elementaryGroup (Fin n) R) :=
  FiniteTypeLeavittTT.elementaryGroup_hasTTmodT
    X f hf L hdiv hdiag n hn

/-- **Binary Leavitt specialization.**  In every rank at least three, the
elementary group over the binary Leavitt algebra over `F₂` has property
`(TT)/T`. -/
theorem binaryLeavitt_elementaryGroup_hasTTmodT
    (n : ℕ) (hn : 3 ≤ n) :
    HasTTmodT.{0, 0}
      (elementaryGroup (Fin n) LeavittAllRanksTT.L) :=
  LeavittAllRanksTT.elementaryGroup_hasTTmodT n hn

end
end PropertyTTPaper
end GroupApproximation
