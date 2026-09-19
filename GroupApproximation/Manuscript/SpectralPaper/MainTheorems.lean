import GroupApproximation.Sofic.AlternatingLampLiteralPackage
import GroupApproximation.Sofic.FinitePerfectLampExactRadical
import GroupApproximation.Sofic.SpectralCompression

/-!
# Closed endpoints for the spectral-compression paper

This file contains the literal, source-closed theorem packages advertised in
the revised paper.  Their proofs only assemble the reusable results in the
analysis and compression-wreath namespaces.
-/

namespace GroupApproximation
namespace SpectralPaper

open MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open AlternatingLampLiteral
open MatricialStabilityRadical

universe u

/-- The exact quantitative spectral-compression statement advertised by the
paper, with every ambient object and hypothesis quantified inside the
proposition. -/
def SpectralCompressionTheorem : Prop :=
  ∀ {E' : Type u} [Group E']
    (L : Subgroup E') (_hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E'} (_hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (_hv : IsStarNormal v)
    (_hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (_horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v)),
    ∀ γ ∈ L,
      ‖Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v - v‖ ≤
        SpectralComponentDiameter.spectralComponentDiameter v

theorem spectralCompressionTheorem : SpectralCompressionTheorem := by
  intro E' _ L hT s hcomp X _ pi v hv hcompressed horbit
  exact SpectralCompression.corona_spectral_component_motion_supremum
    L hT hcomp X pi v hv hcompressed horbit

/-- The zero-dimensional exact-collapse corollary, again as one source-closed
paper endpoint. -/
def ZeroDimensionalSpectralCollapseTheorem : Prop :=
  ∀ {E' : Type u} [Group E']
    (L : Subgroup E') (_hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E'} (_hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (_hv : IsStarNormal v)
    (_hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (_horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v))
    (_hzero : ∀ z : spectrum ℂ v, connectedComponent z = {z}),
    ∀ γ ∈ L,
      Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v = v

theorem zeroDimensionalSpectralCollapseTheorem :
    ZeroDimensionalSpectralCollapseTheorem := by
  intro E' _ L hT s hcomp X _ pi v hv hcompressed horbit hzero
  exact SpectralCompression.corona_zero_dimensional_spectral_collapse
    L hT hcomp X pi v hv hcompressed horbit hzero

/-- Every target class in the unconditional universal-visible-quotient theorem
for an arbitrary finite perfect lamp, collected in one source-closed endpoint. -/
def FinitePerfectUniversalInvisibility : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    (∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
      letI : ∀ n, Nonempty (X n) :=
        fun n ↦ Fintype.card_pos_iff.mp (hX n)
      Function.Bijective
        (precomp
          (SemidirectProduct.rightHom :
            FinitePerfectLamp.WFin K →* Vertical conjD conjD_injective)
          (unitary (NormMatrixCStarCorona (fun n ↦ X n))))) ∧
    (∀ (T : Type) [Group T], IsResiduallyFinite T →
      Function.Bijective
        (precomp
          (SemidirectProduct.rightHom :
            FinitePerfectLamp.WFin K →* Vertical conjD conjD_injective) T)) ∧
    (∀ (T : Type) [Group T] [Finite T],
      Function.Bijective
        (precomp
          (SemidirectProduct.rightHom :
            FinitePerfectLamp.WFin K →* Vertical conjD conjD_injective) T)) ∧
    (∀ (Y : FiniteModel),
      Function.Bijective
        (precomp
          (SemidirectProduct.rightHom :
            FinitePerfectLamp.WFin K →* Vertical conjD conjD_injective)
          (Matrix.unitaryGroup Y ℂ))) ∧
    (∀ (F : Type) [Field F] (d : ℕ),
      Function.Bijective
        (precomp
          (SemidirectProduct.rightHom :
            FinitePerfectLamp.WFin K →* Vertical conjD conjD_injective)
          (Matrix.GeneralLinearGroup (Fin d) F))) ∧
    (∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
      [CompactSpace T] [TotallyDisconnectedSpace T],
      Function.Bijective
        (precomp
          (SemidirectProduct.rightHom :
            FinitePerfectLamp.WFin K →* Vertical conjD conjD_injective) T))

theorem finitePerfectUniversalInvisibility :
    FinitePerfectUniversalInvisibility := by
  intro K _ _ hperfect
  exact ⟨
    fun X hX => FinitePerfectLamp.precomp_bijective_actualCorona
      K hperfect X hX,
    fun T _ hT => FinitePerfectLamp.precomp_bijective_residuallyFinite
      K hperfect T hT,
    fun T _ _ => FinitePerfectLamp.precomp_bijective_finite K hperfect T,
    fun Y => FinitePerfectLamp.precomp_bijective_fdUnitary K hperfect Y,
    fun F _ d => FinitePerfectLamp.precomp_bijective_generalLinearGroup
      K hperfect F d,
    fun T _ _ _ _ _ => FinitePerfectLamp.precomp_bijective_profinite
      K hperfect T⟩

/-- The invisible kernel is intrinsically the ordinary finite-support lamp
group. -/
noncomputable def kernelEquivLamp :
    ↥qA.ker ≃*
      Lamp (alternatingGroup (Fin 5)) (Cosets conjD conjD_injective) := by
  have hker : qA.ker = FinitePerfectLamp.lampSub (alternatingGroup (Fin 5)) :=
    ker_rightHom_eq_lampRange
  exact (MulEquiv.subgroupCongr hker).trans
    (MonoidHom.ofInjective
      (SemidirectProduct.inl_injective
        (N := Lamp (alternatingGroup (Fin 5)) (Cosets conjD conjD_injective))
        (G := Vertical conjD conjD_injective))).symm

/-- The invisible kernel is locally finite, amenable, residually finite, and
MF when regarded as a group in its own right. -/
theorem invisibleKernelTame :
    IsLocallyFiniteGroup qA.ker ∧
      Amenability.IsAmenable qA.ker ∧
      IsResiduallyFinite qA.ker ∧ IsOperatorMF qA.ker := by
  have hlocal : IsLocallyFiniteGroup qA.ker :=
    lamp_isLocallyFiniteGroup.comap kernelEquivLamp.toMonoidHom
      kernelEquivLamp.injective
  exact ⟨hlocal, isAmenable_of_isLocallyFiniteGroup hlocal,
    IsResiduallyFinite.of_injective kernelEquivLamp.toMonoidHom
      kernelEquivLamp.injective lamp_isResiduallyFinite,
    isOperatorMF_of_locallyFinite hlocal⟩

/-- **One invisible relation changes MF.**  The quotient is split, its
nontrivial kernel is normally generated by the explicit involution `rA`, the
source is sofic and non-MF, the quotient is residually finite and MF, and all
four unconditional radicals are exactly that kernel. -/
theorem oneInvisibleRelationPackage :
    qA.ker = Subgroup.normalClosure {rA} ∧
      rA ≠ 1 ∧ rA * rA = 1 ∧
      qA.comp sectionA = MonoidHom.id _ ∧
      IsSofic WA ∧ ¬ IsCDEOperatorMF WA ∧
      IsResiduallyFinite (Vertical conjD conjD_injective) ∧
      IsOperatorMF (Vertical conjD conjD_injective) ∧
      IsLocallyFiniteGroup qA.ker ∧
      Amenability.IsAmenable qA.ker ∧
      IsResiduallyFinite qA.ker ∧ IsOperatorMF qA.ker ∧
      actualCoronaMFResidual WA = qA.ker ∧
      fdUnitaryResidual WA = qA.ker ∧
      finiteResidual WA = qA.ker ∧
      linearResidual WA = qA.ker := by
  have hperfect : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    AlternatingLampFamily.alternating_fin_commutator_eq_top (by omega)
  have hrads := FinitePerfectLamp.four_radicals_eq_lampSub
    (alternatingGroup (Fin 5)) hperfect
  have hker : qA.ker = FinitePerfectLamp.lampSub (alternatingGroup (Fin 5)) :=
    ker_rightHom_eq_lampRange
  exact ⟨AlternatingLampLiteral.ker_rightHom_eq_normalClosure_witnessLamp,
    rA_ne_one, rA_mul_self, qA_comp_sectionA,
    FinitePerfectLamp.isSofic_WFin (alternatingGroup (Fin 5)),
    AlternatingLampLiteral.not_isCDEOperatorMF_WA,
    AlternatingLampFamily.vertical_isResiduallyFinite,
    WitnessVertical.vertical_isOperatorMF,
    invisibleKernelTame.1, invisibleKernelTame.2.1,
    invisibleKernelTame.2.2.1, invisibleKernelTame.2.2.2,
    hrads.1.trans hker.symm,
    hrads.2.1.trans hker.symm,
    hrads.2.2.1.trans hker.symm,
    hrads.2.2.2.trans hker.symm⟩

/-- **Universal invisibility of the same quotient.**  Precomposition with `qA`
is bijective for genuine norm-matrix coronas, finite and residually finite
groups, finite-dimensional unitary and all-fields linear groups, and profinite
groups. -/
theorem a5UniversalInvisibility :
    (∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
      letI : ∀ n, Nonempty (X n) :=
        fun n ↦ Fintype.card_pos_iff.mp (hX n)
      Function.Bijective
        (precomp qA (unitary (NormMatrixCStarCorona (fun n ↦ X n))))) ∧
    (∀ (T : Type) [Group T], IsResiduallyFinite T →
      Function.Bijective (precomp qA T)) ∧
    (∀ (T : Type) [Group T] [Finite T],
      Function.Bijective (precomp qA T)) ∧
    (∀ (Y : FiniteModel),
      Function.Bijective (precomp qA (Matrix.unitaryGroup Y ℂ))) ∧
    (∀ (F : Type) [Field F] (d : ℕ),
      Function.Bijective
        (precomp qA (Matrix.GeneralLinearGroup (Fin d) F))) ∧
    (∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
      [CompactSpace T] [TotallyDisconnectedSpace T],
      Function.Bijective (precomp qA T)) := by
  have hperfect : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    AlternatingLampFamily.alternating_fin_commutator_eq_top (by omega)
  exact ⟨
    fun X hX => FinitePerfectLamp.precomp_bijective_actualCorona
      (alternatingGroup (Fin 5)) hperfect X hX,
    fun T _ hT => FinitePerfectLamp.precomp_bijective_residuallyFinite
      (alternatingGroup (Fin 5)) hperfect T hT,
    fun T _ _ => FinitePerfectLamp.precomp_bijective_finite
      (alternatingGroup (Fin 5)) hperfect T,
    fun Y => FinitePerfectLamp.precomp_bijective_fdUnitary
      (alternatingGroup (Fin 5)) hperfect Y,
    fun F _ d => FinitePerfectLamp.precomp_bijective_generalLinearGroup
      (alternatingGroup (Fin 5)) hperfect F d,
    fun T _ _ _ _ _ => FinitePerfectLamp.precomp_bijective_profinite
      (alternatingGroup (Fin 5)) hperfect T⟩

end SpectralPaper
end GroupApproximation
