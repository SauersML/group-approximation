import GroupApproximation.Sofic.AlternatingLampExactRadical
import GroupApproximation.Sofic.FiveRadicalsCoincide
import GroupApproximation.Sofic.TargetEquivalence
import GroupApproximation.Analysis.PeterWeylProfinite

/-!
# Every nontrivial finite perfect lamp, over the concrete doubling datum

`Sofic/PerfectLampCompressionRadical` proves the exact radical for an abstract
ascending-HNN datum; `Sofic/AlternatingLampExactRadical` instantiates it at
`K = Aₙ`.  The statement the paper displays sits between the two: over the *one*
concrete affine doubling datum, for **every** nontrivial finite perfect lamp
group `K`,

  `Res_MF(K^(V/Γ) ⋊ V) = K^(V/Γ)`,

together with soficity, finite generation, the failure of MF, and the
coincidence of four radicals.  `Aₙ` is then one member of that family rather
than the definition of it.

The fifth (Bohr) column is stated separately and *conditionally*: it takes the
single classical input `PeterWeyl.SeparatesPoints` as a genuine leading
hypothesis, so that the conditionality is visible to the audit's binder check
rather than hidden inside a named proposition.  Nothing else in this file
depends on it.
-/

namespace GroupApproximation
namespace FinitePerfectLamp

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open MatricialStabilityRadical

/-- The compression wreath product of a finite perfect lamp group over the
concrete affine doubling datum. -/
abbrev WFin (K : Type) [Group K] : Type :=
  WreathV (K := K) conjD conjD_injective

instance (K : Type) [Group K] [Finite K] : Countable (WFin K) := inferInstance

/-- The lamp subgroup. -/
abbrev lampSub (K : Type) [Group K] : Subgroup (WFin K) :=
  (inl : Lamp K (Cosets conjD conjD_injective) →* WFin K).range

variable (K : Type) [Group K] [Finite K]

/-- **Theorem C over the concrete datum.**  For a finite perfect lamp group the
MF radical of the compression wreath product is exactly the lamp subgroup. -/
theorem actualCoronaMFResidual_eq_lampSub :
    ∀ (K' : Type) [Group K'] [Finite K'],
      commutator K' = ⊤ → actualCoronaMFResidual (WFin K') = lampSub K' := by
  intro K' _ _ hK
  exact PerfectLampRadical.actualCoronaMFResidual_eq_lampRange conjD
    conjD_injective CommutingLampCollapse.gammaBar_hasKazhdanPropertyT
    (fun k => PerfectLampRadical.exists_pow_eq_one_of_finite k) hK
    v1G_not_mem_range
    ((isCDEOperatorMF_iff_isOperatorMF _).mpr
      WitnessVertical.vertical_isOperatorMF)

/-- The wreath projection's kernel lies in the MF radical. -/
theorem ker_rightHom_le_actualCoronaMFResidual (hK : commutator K = ⊤) :
    (rightHom : WFin K →* Vertical conjD conjD_injective).ker
      ≤ actualCoronaMFResidual (WFin K) := by
  rw [ker_rightHom_eq_lampRange]
  exact PerfectLampRadical.lampRange_le_actualCoronaMFResidual conjD
    conjD_injective CommutingLampCollapse.gammaBar_hasKazhdanPropertyT
    (fun k => PerfectLampRadical.exists_pow_eq_one_of_finite k) hK
    v1G_not_mem_range

instance : Group.FG (WFin K) :=
  MarkedCompression.fg_wreathV conjD conjD_injective
    AlternatingLampFamily.gammaBar_fg inferInstance

/-- Every member of the finite-perfect family is sofic. -/
theorem isSofic_WFin : IsSofic (WFin K) := by
  haveI := ExplicitIntegralLinearModel.gammaBar_residuallyFinite
  exact AscendingHNNWreath.isSofic_wreath_cosets conjD conjD_injective
    isSofic_of_residuallyFinite (isSofic_of_finite' _)

/-- **Four radicals, for every finite perfect lamp.** -/
theorem four_radicals_eq_lampSub (hK : commutator K = ⊤) :
    actualCoronaMFResidual (WFin K) = lampSub K ∧
      fdUnitaryResidual (WFin K) = lampSub K ∧
        finiteResidual (WFin K) = lampSub K ∧
          linearResidual (WFin K) = lampSub K := by
  obtain ⟨h1, h2, h3, h4⟩ := four_radicals_eq
    (rightHom : WFin K →* Vertical conjD conjD_injective)
    AlternatingLampFamily.vertical_isResiduallyFinite
    (ker_rightHom_le_actualCoronaMFResidual K hK)
  rw [ker_rightHom_eq_lampRange] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

omit [Finite K] in
/-- A nontrivial lamp group gives a nontrivial radical. -/
theorem lampSub_ne_bot [Nontrivial K] : lampSub K ≠ ⊥ := by
  obtain ⟨a, ha⟩ := exists_ne (1 : K)
  intro hbot
  have hsingle : Lamp.single (tSite conjD conjD_injective) a ≠ 1 := by
    intro h
    refine ha ?_
    have hval := congrArg
      (fun f : Lamp K (Cosets conjD conjD_injective) =>
        f.toFun (tSite conjD conjD_injective)) h
    simpa using hval
  have hmem : (inl (Lamp.single (tSite conjD conjD_injective) a) : WFin K)
      ∈ lampSub K := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hsingle (inl_injective (by simpa using hmem))

/-- **Every nontrivial finite perfect lamp gives a non-MF group.** -/
theorem not_isCDEOperatorMF_WFin [Nontrivial K] (hK : commutator K = ⊤) :
    ¬ IsCDEOperatorMF (WFin K) := by
  rw [isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot,
    actualCoronaMFResidual_eq_lampSub K hK]
  exact lampSub_ne_bot K

/-- **The finite-perfect package.**  Sofic, finitely generated, not MF, with all
four radicals exactly the lamp subgroup -- for every nontrivial finite perfect
lamp group over the one concrete doubling datum. -/
theorem finitePerfectPackage :
    ∀ (K' : Type) [Group K'] [Finite K'] [Nontrivial K'], commutator K' = ⊤ →
      IsSofic (WFin K') ∧ ¬ IsCDEOperatorMF (WFin K') ∧ Group.FG (WFin K') ∧
        actualCoronaMFResidual (WFin K') = lampSub K' ∧
        fdUnitaryResidual (WFin K') = lampSub K' ∧
        finiteResidual (WFin K') = lampSub K' ∧
        linearResidual (WFin K') = lampSub K' := by
  intro K' _ _ _ hK
  exact ⟨isSofic_WFin K', not_isCDEOperatorMF_WFin K' hK, inferInstance,
    (four_radicals_eq_lampSub K' hK).1, (four_radicals_eq_lampSub K' hK).2.1,
    (four_radicals_eq_lampSub K' hK).2.2.1,
    (four_radicals_eq_lampSub K' hK).2.2.2⟩

/-! ## The universal visible quotient

The radical identities above are equivalently universal statements: restriction
along the split wreath projection is a bijection on Hom-sets for every target
in the finite-dimensional approximation classes used by the paper. -/

/-- Every genuine norm-matrix-corona representation factors uniquely through
the wreath projection. -/
theorem precomp_bijective_actualCorona (hK : commutator K = ⊤)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    Function.Bijective
      (precomp (rightHom : WFin K →* Vertical conjD conjD_injective)
        (unitary (NormMatrixCStarCorona (fun n ↦ X n)))) := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  apply precomp_bijective _ SemidirectProduct.rightHom_surjective
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ actualCoronaMFResidual (WFin K) := by
    rw [actualCoronaMFResidual_eq_lampSub K hK]
    simpa only [lampSub, ker_rightHom_eq_lampRange] using hx
  exact hxrad X hX ρ

/-- Hom-sets into every residually finite target are unchanged. -/
theorem precomp_bijective_residuallyFinite (hK : commutator K = ⊤)
    (T : Type) [Group T] (hT : IsResiduallyFinite T) :
    Function.Bijective
      (precomp (rightHom : WFin K →* Vertical conjD conjD_injective) T) := by
  apply precomp_bijective _ SemidirectProduct.rightHom_surjective
  apply invisibleTo_of_ker_le_finiteResidual
  · rw [ker_rightHom_eq_lampRange, (four_radicals_eq_lampSub K hK).2.2.1]
  · exact hT

/-- Hom-sets into every finite target are unchanged. -/
theorem precomp_bijective_finite (hK : commutator K = ⊤)
    (T : Type) [Group T] [Finite T] :
    Function.Bijective
      (precomp (rightHom : WFin K →* Vertical conjD conjD_injective) T) :=
  precomp_bijective_residuallyFinite K hK T (isResiduallyFinite_of_finite T)

/-- Hom-sets into every finite-dimensional unitary group are unchanged. -/
theorem precomp_bijective_fdUnitary (hK : commutator K = ⊤)
    (Y : FiniteModel) :
    Function.Bijective
      (precomp (rightHom : WFin K →* Vertical conjD conjD_injective)
        (Matrix.unitaryGroup Y ℂ)) := by
  apply precomp_bijective _ SemidirectProduct.rightHom_surjective
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ fdUnitaryResidual (WFin K) := by
    rw [(four_radicals_eq_lampSub K hK).2.1]
    simpa only [lampSub, ker_rightHom_eq_lampRange] using hx
  exact mem_fdUnitaryResidual_iff.mp hxrad Y ρ

/-- Hom-sets into `GL_d(F)` are unchanged for every field and every finite
dimension. -/
theorem precomp_bijective_generalLinearGroup (hK : commutator K = ⊤)
    (F : Type) [Field F] (d : ℕ) :
    Function.Bijective
      (precomp (rightHom : WFin K →* Vertical conjD conjD_injective)
        (Matrix.GeneralLinearGroup (Fin d) F)) := by
  apply precomp_bijective _ SemidirectProduct.rightHom_surjective
  apply invisibleTo_generalLinearGroup_of_ker_le_linearResidual
  rw [ker_rightHom_eq_lampRange, (four_radicals_eq_lampSub K hK).2.2.2]

/-- Every homomorphism into a profinite group kills the lamp kernel, hence
precomposition with the wreath projection is bijective. -/
theorem precomp_bijective_profinite (hK : commutator K = ⊤)
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [CompactSpace T] [TotallyDisconnectedSpace T] :
    Function.Bijective
      (precomp (rightHom : WFin K →* Vertical conjD conjD_injective) T) := by
  apply precomp_bijective _ SemidirectProduct.rightHom_surjective
  intro ρ
  have hfinite := PeterWeyl.finiteResidual_le_ker_of_profinite ρ
  rw [(four_radicals_eq_lampSub K hK).2.2.1] at hfinite
  simpa only [lampSub, ker_rightHom_eq_lampRange] using hfinite

/-! ## The fifth column, conditionally

`PeterWeyl.SeparatesPoints` enters as a genuine leading hypothesis, not as a
clause inside a named proposition.  That is deliberate: the audit's binder check
must be able to see that this statement, unlike every other one in the package,
is not closed. -/

/-- **Five radicals, given the separation core of Peter--Weyl.**  The Bohr
kernel joins the other four exactly when finite-dimensional unitary
representations separate the points of a compact group.  That input is isolated
and is proved nowhere in this development. -/
theorem five_radicals_eq_lampSub_of_separatesPoints
    (hPW : PeterWeyl.SeparatesPoints.{0}) (hK : commutator K = ⊤) :
    actualCoronaMFResidual (WFin K) = lampSub K ∧
      fdUnitaryResidual (WFin K) = lampSub K ∧
        finiteResidual (WFin K) = lampSub K ∧
          linearResidual (WFin K) = lampSub K ∧
            PeterWeyl.bohrResidual (WFin K) = lampSub K := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := five_radicals_eq hPW
    (rightHom : WFin K →* Vertical conjD conjD_injective)
    AlternatingLampFamily.vertical_isResiduallyFinite
    (ker_rightHom_le_actualCoronaMFResidual K hK)
  rw [ker_rightHom_eq_lampRange] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end FinitePerfectLamp
end GroupApproximation
