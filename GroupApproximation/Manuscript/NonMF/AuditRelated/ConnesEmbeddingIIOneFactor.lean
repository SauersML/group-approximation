import GroupApproximation.Manuscript.NonMF.AuditRelated.UltraproductUnitaryLift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.InfiniteSimpleICC
import GroupApproximation.Analysis.GroupVonNeumannUnitaryGroup
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarNotNuclear
import GroupApproximation.Manuscript.NonMF.PriorWorkConnesEmbedding
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.NormMFResidualDetector
import GroupApproximation.Meta.AxiomGuard

/-!
# A II₁ factor embedding in no norm ultraproduct of matrix algebras

`non_mf_groups_exist.tex`, Related work, lines 327--332 (census row
`abfcbcb3af2b`):

> The MF problem itself was answered negatively in 2020: the failure of the
> Connes embedding problem [MIPRE] yields a II_1 factor that embeds in no
> norm ultraproduct of matrix algebras, hence a separable stably finite
> C*-algebra that is not MF [GoldbringHart, Prop 6.1, Rem 6.2].

The sentence asserts two mathematical facts: there is a II₁ factor that
admits no injective (possibly nonunital) `*`-homomorphism into any norm
ultraproduct `∏_ω M_{k_n}`, and there is a separable stably finite
C*-algebra that is not MF.  The second is the existing unconditional theorem
`PriorWork.printedNegativeConnesEmbeddingSentence`.  This module proves the
first unconditionally, with the manuscript's own group in place of the
MIP*=RE factor (the attribution to [MIPRE] is provenance and is not
formalized):

* `cornerCorrectedUnitary`: a nonunital `*`-homomorphism `e` induces
  `u ↦ e u + (1 - e 1)` on unitary groups, injective when `e` is.
* `not_injective_groupVonNeumann_to_ultraproduct`: if the norm-MF residual of
  `G` is all of `G` and `G ≠ 1`, then `L(G)` embeds in no norm ultraproduct.
  Route: `G → U(L(G)) → U(∏_ω M_{k_n}) ≅ UniversalWeakMF ω X`
  (`ultraproductUnitaryEquiv`) is injective, but kills the residual.
* `manuscriptSentence_negativeMFProblemIIOneFactor`: the rank-twelve group `H`
  is infinite and simple, so `L(H)` is a II₁ factor; its corona MF residual is
  everything and `defect ≠ 1`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace AuditRelated

universe u v

noncomputable section

/-- A nonunital `*`-homomorphism sends a unitary to a unitary after adjoining
the complement of the image of the source unit. -/
def cornerCorrectedUnitary {A : Type u} {B : Type v}
    [Ring A] [StarRing A] [Module ℂ A] [Ring B] [StarRing B] [Module ℂ B]
    (e : A →⋆ₙₐ[ℂ] B) : unitary A →* unitary B where
  toFun u := ⟨e (u : A) + (1 - e 1), by
    let x : B := e (u : A)
    let p : B := e 1
    have hp_star : star p = p := by
      change star (e 1) = e 1
      rw [← map_star]
      simp
    have hp_mul : p * p = p := by
      change e 1 * e 1 = e 1
      rw [← map_mul]
      simp
    have hpx : p * x = x := by
      change e 1 * e (u : A) = e (u : A)
      rw [← map_mul]
      simp
    have hxp : x * p = x := by
      change e (u : A) * e 1 = e (u : A)
      rw [← map_mul]
      simp
    have hstarxp : star x * p = star x := by
      have h := congrArg star hpx
      simpa only [star_mul, hp_star, star_star] using h
    have hpstarx : p * star x = star x := by
      have h := congrArg star hxp
      simpa only [star_mul, hp_star, star_star] using h
    have hstarx_mul_x : star x * x = p := by
      change star (e (u : A)) * e (u : A) = e 1
      rw [← map_star, ← map_mul]
      exact congrArg e u.property.1
    have hx_mul_starx : x * star x = p := by
      change e (u : A) * star (e (u : A)) = e 1
      rw [← map_star, ← map_mul]
      exact congrArg e u.property.2
    change
      star (x + (1 - p)) * (x + (1 - p)) = 1 ∧
        (x + (1 - p)) * star (x + (1 - p)) = 1
    rw [star_add, star_sub, star_one, hp_star]
    constructor <;>
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul,
        hstarxp, hpstarx, hpx, hxp, hp_mul, hstarx_mul_x,
        hx_mul_starx] <;>
      noncomm_ring⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    change e ((u : A) * (v : A)) + (1 - e 1) =
      (e (u : A) + (1 - e 1)) * (e (v : A) + (1 - e 1))
    rw [map_mul]
    have hu : e (u : A) * e 1 = e (u : A) := by
      rw [← map_mul]
      simp
    have hv : e 1 * e (v : A) = e (v : A) := by
      rw [← map_mul]
      simp
    have hp : e 1 * e 1 = e 1 := by
      rw [← map_mul]
      simp
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul,
      hu, hv, hp]
    noncomm_ring

/-- Injectivity of the `*`-homomorphism gives injectivity on unitary groups. -/
theorem cornerCorrectedUnitary_injective {A : Type u} {B : Type v}
    [Ring A] [StarRing A] [Module ℂ A] [Ring B] [StarRing B] [Module ℂ B]
    {e : A →⋆ₙₐ[ℂ] B} (he : Function.Injective e) :
    Function.Injective (cornerCorrectedUnitary e) := by
  intro a b hab
  apply Subtype.ext
  apply he
  have h := congrArg Subtype.val hab
  change e (a : A) + (1 - e 1) = e (b : A) + (1 - e 1) at h
  exact add_right_cancel h

/-- **A group whose norm-MF residual is everything has a group von Neumann
algebra embedding in no norm ultraproduct of matrix algebras**, provided the
group is nontrivial. -/
theorem not_injective_groupVonNeumann_to_ultraproduct {G : Type} [Group G]
    (hres : normMFResidual G = ⊤) {g : G} (hg : g ≠ 1)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
    (f : ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra →⋆ₙₐ[ℂ]
      FilterMatrixCStarCorona (fun n ↦ X n) (ω : Filter ℕ)) :
    ¬ Function.Injective f := by
  intro hf
  let rho : G →* UniversalWeakMF ω X :=
    (ultraproductUnitaryEquiv X ω).symm.toMonoidHom.comp
      ((cornerCorrectedUnitary f).comp (GroupVonNeumann.leftRegularUnitaryHom G))
  have hrho : Function.Injective rho := by
    intro a b hab
    apply GroupVonNeumann.leftRegularUnitaryHom_injective G
    apply cornerCorrectedUnitary_injective hf
    exact (ultraproductUnitaryEquiv X ω).symm.injective hab
  have hmem : g ∈ normMFResidual G := by
    rw [hres]
    exact Subgroup.mem_top g
  apply hg
  apply hrho
  rw [map_eq_one_of_mem_normMFResidual ω X rho hmem, map_one]

/-- **tex 327--332.**  There is a II₁ factor that embeds (by an injective,
possibly nonunital `*`-homomorphism) in no norm ultraproduct of matrix
algebras, and there is a separable stably finite C*-algebra that is not MF. -/
theorem manuscriptSentence_negativeMFProblemIIOneFactor :
    (∃ (G : Type) (_ : Group G),
      IIOneFactor.IsIIOneFactor (GroupVonNeumann.groupVonNeumannAlgebra G) ∧
        ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
          (f : ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra →⋆ₙₐ[ℂ]
            FilterMatrixCStarCorona (fun n ↦ X n) (ω : Filter ℕ)),
          ¬ Function.Injective f) ∧
      OneSidedMFRadical.SeparableStablyFiniteNonMFCStarAlgebraExists := by
  have hres : normMFResidual OneSidedMFRadical.RankTwelveEndpoint.H = ⊤ := by
    haveI : Countable OneSidedMFRadical.RankTwelveEndpoint.H :=
      OneSidedMFRadical.RankTwelveEndpoint.countable
    rw [← coronaMFResidual_eq_normMFResidual, ← actualCoronaMFResidual_eq_coronaMFResidual]
    exact OneSidedMFRadical.RankTwelveEndpoint.rankTwelve_actualCoronaMFResidual_eq_top
  refine ⟨⟨OneSidedMFRadical.RankTwelveEndpoint.H, inferInstance,
    SimpleKazhdanSofic.printedInfiniteSimpleGroupVonNeumannIIOneFactor
      OneSidedMFRadical.RankTwelveEndpoint.H
      OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionSimple
      OneSidedMFRadical.rankTwelveEndpoint_infinite, ?_⟩,
    PriorWork.printedNegativeConnesEmbeddingSentence.1⟩
  intro X _ ω f
  exact not_injective_groupVonNeumann_to_ultraproduct hres
    OneSidedMFRadical.RankTwelveEndpoint.defect_ne_one X ω f

end

end AuditRelated
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.cornerCorrectedUnitary
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.cornerCorrectedUnitary_injective
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.not_injective_groupVonNeumann_to_ultraproduct
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.manuscriptSentence_negativeMFProblemIIOneFactor
