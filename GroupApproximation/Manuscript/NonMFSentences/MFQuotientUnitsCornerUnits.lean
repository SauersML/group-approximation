import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsStepOne
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingFullIdeal
import GroupApproximation.Algebra.PurelyInfiniteSimpleRingIdempotents
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`: the corner ring `eRe`, and `eq:corner-units`, at the printed objects

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units` (tex 1242–1253):

> Every nonzero idempotent `e` of `R` is infinite [AGP, Proposition 1.5], so `eRe` contains
> `s, t` with `ts = e ≠ st`, and `eRe` is simple, so `e - st` generates `eRe` as a two-sided
> ideal; hence every homomorphism from `EL_m(eRe)`, `m ≥ 2`, to an MF group is trivial.
> Consequently, if `e` and `P` are nonzero idempotents and `θ : M_m(eRe) → PRP` is a ring
> isomorphism, then `1 - P + θ(A) ∈ N` for `A ∈ EL_m(eRe)`, since these units form the image
> of `EL_m(eRe)` under a homomorphism to `H`.

The census carriers of these sentences (`MFQuotientUnitsSentences.manuscriptSentence_cornerElementaryKillsMFTargets`,
`manuscriptSentence_cornerUnitsLieInRadical`) state the consumed conclusions for an abstract
ring and for the subgroup `cornerUnitSubgroup`, without the corner `eRe`, the idempotent `P`
or the ring isomorphism `θ`.  This module states both sentences at the printed objects:

* `manuscriptSentence_cornerRing`: for a nonzero idempotent `e` of a countable purely
  infinite simple ring, `e` is infinite, the corner ring `eRe` (`Corner R e he`, whose unit is
  `e`) contains `s, t` with `ts = 1_{eRe} = e ≠ st` and `1_{eRe} - st` full, `eRe` is simple,
  and every homomorphism from `EL_m(eRe)`, `m ≥ 2`, to an MF group is trivial;
* `cornerUnitsHom`: the printed map `A ↦ 1 - P + θ(A)`, a group homomorphism
  `EL_m(eRe) → Rˣ`;
* `manuscriptSentence_cornerUnits`: `eq:corner-units`, with its printed justification: the
  units `1 - P + θ(A)` form the image of `EL_m(eRe)` under that homomorphism, hence lie in
  `N = Rad_MF(Rˣ)`.

Nothing is assumed: Ara--Goodearl--Pardo Proposition 1.5 is `isInfiniteIdempotent_of_ne_zero`,
simplicity of corners is `isSimpleRing_corner`, fullness in a simple ring is
`FullDefectRing.isSimpleRing_full_of_not_directlyFinite`, and Theorem `thm:full-defect-ring`
in rank two is `FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics`.
-/

namespace GroupApproximation
namespace MFQuotientUnitsCornerUnits

open MFQuotientUnits
open Manuscript.OneSidedMFRadical

/-! ## The corner ring `eRe` -/

/-- **Printed (tex 1242–1246).**  For a nonzero idempotent `e` of a countable purely
infinite simple ring `R`: `e` is infinite; `eRe` contains `s, t` with `ts = e ≠ st`, and
`e - st` generates `eRe` as a two-sided ideal; `eRe` is simple; and every homomorphism from
`EL_m(eRe)`, `m ≥ 2`, to an MF group is trivial.  In the corner ring the unit is `e`, so
`ts = e` reads `t * s = 1`. -/
def PrintedCornerRing : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (e : R) (he : IsIdempotentElem e), e ≠ 0 →
      IsInfiniteIdempotent R e ∧
        (∃ s t : Corner R e he, t * s = 1 ∧ s * t ≠ 1 ∧
          ∃ (m : ℕ) (a b : Fin m → Corner R e he), ∑ k, a k * (1 - s * t) * b k = 1) ∧
        IsSimpleRing (Corner R e he) ∧
        ∀ m : ℕ, 2 ≤ m → ∀ (M : Type) [Group M], IsOperatorMF M →
          ∀ (f : elementaryGroup (Fin m) (Corner R e he) →* M)
            (x : elementaryGroup (Fin m) (Corner R e he)), f x = 1

theorem manuscriptSentence_cornerRing : PrintedCornerRing := by
  intro R _ _ hR e he hne
  have hinf : IsInfiniteIdempotent R e := isInfiniteIdempotent_of_ne_zero hR he hne
  haveI : IsSimpleRing (Corner R e he) := isSimpleRing_corner hR he hne
  obtain ⟨s, t, hts, hst⟩ := exists_properIsometry_corner he hinf
  obtain ⟨-, hfull⟩ := FullDefectRing.isSimpleRing_full_of_not_directlyFinite hts hst
  refine ⟨hinf, ⟨s, t, hts, hst, hfull⟩, inferInstance, ?_⟩
  intro m hm M _ hM f x
  exact FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
    (Corner R e he) s t hts hfull m hm M hM f x

/-! ## `eq:corner-units` -/

/-- **The printed map `A ↦ 1 - P + θ(A)`** from `EL_m(eRe)` to the units of `R`, for a ring
isomorphism `θ : M_m(eRe) → PRP`: the inclusion of `EL_m(eRe)` in `GL_m(eRe)`, then `θ` on
units, then the extension of a unit of `PRP` by the complementary identity. -/
noncomputable def cornerUnitsHom {R : Type} [Ring R] {e P : R} (he : IsIdempotentElem e)
    (hP : IsIdempotentElem P) {m : ℕ}
    (θ : Matrix (Fin m) (Fin m) (Corner R e he) ≃+* Corner R P hP) :
    elementaryGroup (Fin m) (Corner R e he) →* Rˣ :=
  (unitOfCornerUnit P hP).comp
    ((Units.map θ.toMonoidHom).comp (elementaryGroup (Fin m) (Corner R e he)).subtype)

@[simp] theorem coe_cornerUnitsHom {R : Type} [Ring R] {e P : R} (he : IsIdempotentElem e)
    (hP : IsIdempotentElem P) {m : ℕ}
    (θ : Matrix (Fin m) (Fin m) (Corner R e he) ≃+* Corner R P hP)
    (A : elementaryGroup (Fin m) (Corner R e he)) :
    ((cornerUnitsHom he hP θ A : Rˣ) : R) =
      1 - P + ((θ ((A : (Matrix (Fin m) (Fin m) (Corner R e he))ˣ) :
        Matrix (Fin m) (Fin m) (Corner R e he)) : Corner R P hP) : R) := rfl

/-- **Printed display `eq:corner-units` (tex 1246–1253).**  If `e` and `P` are nonzero
idempotents and `θ : M_m(eRe) → PRP` is a ring isomorphism, then `1 - P + θ(A) ∈ N` for every
`A ∈ EL_m(eRe)`, `m ≥ 2`; and these units are the values of one homomorphism
`EL_m(eRe) → H`, the printed justification. -/
def PrintedCornerUnits : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (e P : R) (he : IsIdempotentElem e) (hP : IsIdempotentElem P), e ≠ 0 → P ≠ 0 →
      ∀ (m : ℕ), 2 ≤ m →
        ∀ θ : Matrix (Fin m) (Fin m) (Corner R e he) ≃+* Corner R P hP,
          ∃ φ : elementaryGroup (Fin m) (Corner R e he) →* Rˣ,
            (∀ A : elementaryGroup (Fin m) (Corner R e he),
              ((φ A : Rˣ) : R) = 1 - P + ((θ ((A : (Matrix (Fin m) (Fin m) (Corner R e he))ˣ) :
                Matrix (Fin m) (Fin m) (Corner R e he)) : Corner R P hP) : R)) ∧
            φ.range ≤ MFQuotientUnits.mfHomKernel Rˣ

theorem manuscriptSentence_cornerUnits : PrintedCornerUnits := by
  intro R _ _ hR e P he hP hne _hPne m hm θ
  refine ⟨cornerUnitsHom he hP θ, fun A => coe_cornerUnitsHom he hP θ A, ?_⟩
  refine range_le_mfHomKernel (cornerUnitsHom he hP θ) ?_
  intro M _ hM f x
  exact (manuscriptSentence_cornerRing R hR e he hne).2.2.2 m hm M hM f x

end MFQuotientUnitsCornerUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsCornerUnits.manuscriptSentence_cornerRing
#audit_axioms GroupApproximation.MFQuotientUnitsCornerUnits.coe_cornerUnitsHom
#audit_closed_axioms GroupApproximation.MFQuotientUnitsCornerUnits.manuscriptSentence_cornerUnits
