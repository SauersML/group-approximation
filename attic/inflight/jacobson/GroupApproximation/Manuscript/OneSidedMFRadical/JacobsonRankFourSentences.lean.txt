import GroupApproximation.Leavitt.OneSidedCompressor
import GroupApproximation.PropertyT.IntegralColumnPlaneClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Why rank four: three coordinates for property `(T)`, one for the compressor

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1145--1146 and 1155--1157):

> The rank four is three plus one. … Three coordinates carry
> property~(T)~[EJZ, Theorem 1.1], and the fourth makes the compression by `s`
> invertible.

Both halves are already theorems of the repository; this module states them as
the printed sentences.

* **Three coordinates carry `(T)`.**  For every finitely generated unital ring
  the core `L = EL_3(A)`, in coordinates `0,1,2` of `EL_4(A)`, has property `(T)`:
  Ershov--Jaikin-Zapirain's theorem is proved in the repository
  (`IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`)
  and transported to the core (`OneSidedCompressor.core_hasKazhdanPropertyT`).
* **Three plus one.**  `EL_3(A)` embeds in `EL_4(A)` onto the core, and the spare
  coordinate `3` is none of the core coordinates.
* **The fourth coordinate makes the compression invertible.**  For every pair
  `t s = 1`, the element `u ∈ EL_4(A)` built on the spare coordinate conjugates
  `e_{ij}(a)` to `e_{ij}(s a t)` on the core, so `u L u⁻¹ ≤ L`: the compression
  `a ↦ s a t` of the coefficients is realized by an invertible matrix.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonRankFour

open OneSidedCompressor

/-- **Printed (tex 1155--1156).**  "Three coordinates carry property (T)": for every
finitely generated unital ring `A`, the core `EL_3(A)` in coordinates `0,1,2` of
`EL_4(A)` has property `(T)`. -/
theorem manuscriptSentence_threeCoordinatesCarryPropertyT :
    ∀ (A : Type) [Ring A], IsFinitelyGeneratedRing A → HasKazhdanPropertyT.{0, 0} (core A) :=
  fun A _ hA ↦ core_hasKazhdanPropertyT
    (IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT A hA 3 le_rfl)

/-- **Printed (tex 1145--1146 and 1156--1157).**  "The rank four is three plus
one … and the fourth makes the compression by `s` invertible": `EL_3(A)` embeds
onto the core of `EL_4(A)`, the fourth coordinate is outside the core, and the
compressor `u ∈ EL_4(A)` of a pair `t s = 1` conjugates `e_{ij}(a)` to
`e_{ij}(s a t)` on the core, so `u L u⁻¹ ≤ L`. -/
theorem manuscriptSentence_fourthCoordinateMakesCompressionInvertible :
    ∀ (A : Type) [Ring A] (P : OneSidedInverse A),
      Function.Injective (coreEmbedding (R := A)) ∧ (coreEmbedding (R := A)).range = core A ∧
        (∀ i : Fin 3, coreIdx i ≠ lastIdx) ∧
        (∀ (i j : Fin 3) (hij : i ≠ j) (a : A),
          compressor P * elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a *
              (compressor P)⁻¹ =
            elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) (P.s * a * P.t)) ∧
        ∀ g ∈ core A, compressor P * g * (compressor P)⁻¹ ∈ core A :=
  fun _ _ P ↦ ⟨coreEmbedding_injective, coreEmbedding_range, coreIdx_ne_last,
    compressor_conj_root P, compressor_compresses_core P⟩

end JacobsonRankFour
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankFour.manuscriptSentence_threeCoordinatesCarryPropertyT
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankFour.manuscriptSentence_fourthCoordinateMakesCompressionInvertible
