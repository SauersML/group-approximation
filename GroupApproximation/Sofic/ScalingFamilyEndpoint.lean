import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.ScalingFamilyLinearWitness

/-!
# The non-MF endpoint for the whole scaling family

`LiteralNonMFEndpoint` runs the unconditional argument for the single
presentation with stable relations `t vᵢ t⁻¹ = vᵢ²`.  Both halves of that
argument are insensitive to the exponent:

* the Kazhdan half uses only property `(T)` of the literal base and the
  containment `t · iota(Base) · t⁻¹ ⊆ iota(Base)`, and the base and its
  property `(T)` do not depend on `m` at all; and
* the separating half is the explicit affine--Clifford witness, which
  `ScalingFamilyLinearWitness` supplies for every `m ≥ 2`.

So the entire pipeline runs uniformly in `m`, and every member with `m ≥ 2`
is a finitely presented non-MF group.  Specializing at `m = 2` returns the
declarations of `LiteralNonMFEndpoint` (`relators_two` identifies the group
itself on the nose).

Nothing here is conditional: no property-`(T)` hypothesis, no literature
input, no axioms beyond Lean's own.
-/

namespace GroupApproximation
namespace ScalingFamilyEndpoint

open LiteralNonMFPresentation
open ScalingFamilyPresentation
open ReducedGroupCStarTrace
open scoped commutatorElement

noncomputable section

variable {m : ℕ}

/-! ## The marked-compression datum of the `m`-th member -/

/-- The exact marked-compression datum for the `m`-th group of the family.
Its property-`(T)` field is discharged by the premise-free P13 bridge, which
is a statement about the base alone and therefore identical for every `m`. -/
noncomputable def familyInclusionData (m : ℕ) :
    MarkedCompressionInclusionData Base (MarkedGroup m) where
  iota := baseMap m
  t := stable m
  c := lamp m
  a := PresentedGroup.of v1Index
  kazhdan := LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT
  compresses gamma := by
    obtain ⟨delta, hdelta⟩ := stable_conjugates_base_into_base m gamma
    exact ⟨delta, hdelta.symm⟩
  comm_c := lamp_commutes_base m
  word_sq := by
    rw [← mark_eq_markedCompressionWord m]
    exact mark_sq m
  word_central g := by
    rw [← mark_eq_markedCompressionWord m]
    exact mark_central m g

@[simp] theorem familyInclusionData_word (m : ℕ) :
    (familyInclusionData m).word = mark m :=
  (mark_eq_markedCompressionWord m).symm

/-- At `m = 2` this is the literal manuscript datum. -/
@[simp] theorem familyInclusionData_two :
    familyInclusionData 2 = LiteralNonMFEndpoint.inclusionData := rfl

/-- The transported involution `d = t c t⁻¹`. -/
abbrev compressionRoot (m : ℕ) : MarkedGroup m :=
  (familyInclusionData m).toKazhdanCompressionCore.transported

/-- The distinguished pointwise compression defect `u = [d,a]`. -/
abbrev compressionDefect (m : ℕ) : MarkedGroup m :=
  ⁅compressionRoot m, (familyInclusionData m).iota (familyInclusionData m).a⁆

/-! ## The algebraic box: `w = u²` -/

/-- The `m`-th mark is the square of the distinguished compression defect. -/
theorem mark_eq_compressionDefect_sq (m : ℕ) :
    mark m = compressionDefect m ^ 2 := by
  have h := (familyInclusionData m).word_eq_compressionDefect_sq (lamp_sq m)
  rw [familyInclusionData_word] at h
  exact h

/-- The same identity in the manuscript's own notation. -/
theorem mark_eq_rootCommutator_sq (m : ℕ) :
    mark m =
      ⁅stable m * lamp m * (stable m)⁻¹,
        baseMap m (PresentedGroup.of v1Index)⁆ ^ 2 :=
  mark_eq_compressionDefect_sq m

/-- The square identity together with the Clifford realization. -/
theorem compressionDefect_sq_ne_one (hm : 2 ≤ m) :
    compressionDefect m ^ 2 ≠ 1 := by
  rw [← mark_eq_compressionDefect_sq]
  exact ScalingFamilyLinearWitness.scaling_mark_ne_one hm

/-! ## Kazhdan pinning -/

/-- Every pointwise compression defect converges to the identity in
normalized Hilbert--Schmidt distance in every operator-norm almost
representation. -/
theorem kazhdanPinning (m : ℕ) (B : OpAlmostRepresentation (MarkedGroup m)) :
    KazhdanCompressionCore.CompressionDefectsHSTrivial
      (familyInclusionData m).toKazhdanCompressionCore B :=
  (familyInclusionData m).toKazhdanCompressionCore.compressionDefects_hsTrivial B

/-- A separated negative corner for the `m`-th mark contradicts Kazhdan
transport and the identity `mark = compressionDefect²`. -/
theorem negativeCorner_kazhdanTransport_contradiction (m : ℕ)
    (A : MarkedOpAlmostRepresentation (MarkedGroup m) (mark m)) : False := by
  rw [← familyInclusionData_word] at A
  exact KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation
    (familyInclusionData m) A

/-! ## The explicit finite normal subgroup `{1, mark}` -/

/-- The central-involution subgroup used in the finite-normal obstruction. -/
noncomputable def familyInvolutionSubgroup (m : ℕ) : Subgroup (MarkedGroup m) :=
  centralInvolutionSubgroup (mark m) (mark_sq m)

@[simp] theorem mem_familyInvolutionSubgroup_iff (m : ℕ) (g : MarkedGroup m) :
    g ∈ familyInvolutionSubgroup m ↔ g = 1 ∨ g = mark m :=
  Iff.rfl

@[simp] theorem coe_familyInvolutionSubgroup (m : ℕ) :
    (familyInvolutionSubgroup m : Set (MarkedGroup m)) = {1, mark m} :=
  coe_centralInvolutionSubgroup (mark m) (mark_sq m)

@[simp] theorem mark_mem_familyInvolutionSubgroup (m : ℕ) :
    mark m ∈ familyInvolutionSubgroup m :=
  involution_mem_centralInvolutionSubgroup (mark m) (mark_sq m)

noncomputable instance familyInvolutionSubgroup_finite (m : ℕ) :
    Finite (familyInvolutionSubgroup m) :=
  centralInvolutionSubgroup_finite (mark m) (mark_sq m)

instance familyInvolutionSubgroup_normal (m : ℕ) :
    (familyInvolutionSubgroup m).Normal :=
  centralInvolutionSubgroup_normal (mark m) (mark_sq m) (mark_central m)

/-- The central-involution subgroup belongs to the normal closure of the pinned
compression defects. -/
theorem familyInvolutionSubgroup_le_defectNormal (m : ℕ) :
    familyInvolutionSubgroup m ≤
      (familyInclusionData m).toKazhdanCompressionCore.defectNormal := by
  rw [familyInvolutionSubgroup,
    centralInvolutionSubgroup_le_iff_mem (mark m) (mark_sq m)]
  rw [← familyInclusionData_word]
  exact (familyInclusionData m).word_mem_compressionDefectNormal

/-! ## Corona annihilation -/

/-- Every homomorphism into the unitary group of a genuine positive-size
norm-matrix C-star corona kills `{1, mark}`. -/
theorem familyInvolutionSubgroup_le_normMatrixCStarCoronaKernel (m : ℕ)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : MarkedGroup m →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      familyInvolutionSubgroup m ≤ rho.ker := by
  exact KazhdanCompressionCore.finiteNormal_le_normMatrixCStarCoronaKernel
    (familyInclusionData m).toKazhdanCompressionCore
    (familyInvolutionSubgroup m) (familyInvolutionSubgroup_le_defectNormal m) X hX

/-- Every homomorphism into every positive-size unitary-sequence norm corona
kills `{1, mark}`. -/
theorem familyInvolutionSubgroup_le_normMatrixCoronaKernel (m : ℕ)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : MarkedGroup m →* NormMatrixCoronaUnitary X) :
    familyInvolutionSubgroup m ≤ rho.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  let kappa : NormMatrixCoronaUnitary X →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (normMatrixCoronaUnitaryEquiv X).toMonoidHom
  intro f hf
  have hactual : f ∈ (kappa.comp rho).ker :=
    familyInvolutionSubgroup_le_normMatrixCStarCoronaKernel
      m X hX (kappa.comp rho) hf
  apply MonoidHom.mem_ker.mpr
  apply (normMatrixCoronaUnitaryEquiv X).injective
  change kappa (rho f) = kappa 1
  have hkappa : kappa (rho f) = 1 := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      MonoidHom.mem_ker.mp hactual
  rw [hkappa, map_one]

/-- The genuine C-star-corona statement in literal natural matrix
coordinates. -/
theorem scaling_mark_eq_one_in_CStarCorona (m : ℕ)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    ∀ rho : MarkedGroup m →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      rho (mark m) = 1 := by
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro rho
  exact MonoidHom.mem_ker.mp
    (KazhdanCompressionCore.defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel
      (familyInclusionData m).toKazhdanCompressionCore
      (familyInclusionData m).a (mark m)
      (mark_eq_compressionDefect_sq m) (mark_sq m) (mark_central m)
      (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd) rho)

/-- The unitary-sequence-corona clause, in literal natural-number
dimensions. -/
theorem scaling_mark_eq_one_in_unitaryCorona (m : ℕ)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (Theta : MarkedGroup m →*
      NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (d n))) :
    Theta (mark m) = 1 :=
  MonoidHom.mem_ker.mp
    (KazhdanCompressionCore.defectSquare_centralInvolution_mem_normMatrixCoronaKernel
      (familyInclusionData m).toKazhdanCompressionCore
      (familyInclusionData m).a (mark m)
      (mark_eq_compressionDefect_sq m) (mark_sq m) (mark_central m)
      (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd) Theta)

/-- The `m`-th mark belongs to the MF radical exactly as printed. -/
theorem scaling_mark_mem_manuscriptCoronaMFResidual (m : ℕ) :
    mark m ∈ manuscriptCoronaMFResidual (MarkedGroup m) :=
  (mem_manuscriptCoronaMFResidual_iff (G := MarkedGroup m)).2
    (scaling_mark_eq_one_in_CStarCorona m)

/-- The mark also belongs to the basis-free unitary-sequence MF residual. -/
theorem scaling_mark_normMFInvisible (m : ℕ) : NormMFInvisible (mark m) :=
  KazhdanCompressionCore.defectSquare_centralInvolution_normMFInvisible
    (familyInclusionData m).toKazhdanCompressionCore
    (familyInclusionData m).a (mark m)
    (mark_eq_compressionDefect_sq m) (mark_sq m) (mark_central m)

/-! ## Premise-free MF and C-star consequences -/

/-- The corona obstruction and the Clifford detector in one statement. -/
theorem cliffordSign_blackHole (hm : 2 ≤ m) :
    NormMFInvisible (mark m) ∧ mark m ≠ 1 :=
  ⟨scaling_mark_normMFInvisible m,
    ScalingFamilyLinearWitness.scaling_mark_ne_one hm⟩

/-- **The central-sign criterion at the `m`-th datum.**  Exactly as for the
literal group, the manuscript's closed criterion is instantiated at
`Γ = Base`, `E = MarkedGroup m`, `ι = baseMap m`, `t = stable m`,
`c = lamp m`, `a = v₁`, and `z = mark m`. -/
theorem scaling_centralSignCriterion (m : ℕ) (hm : 2 ≤ m) :
    (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ rho : MarkedGroup m →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho (mark m) = 1) ∧
      ¬ IsCDEOperatorMF (MarkedGroup m) :=
  -- Two universe levels: the ambient group's, then the property-`(T)`
  -- Hilbert-space universe.  Both are `0` for the scaling family.
  KazhdanCompressionCore.manuscriptCentralSignCriterion.{0, 0}
    (Γ := Base) (E := MarkedGroup m)
    LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT.2
    (baseMap m) (stable m) (lamp m) (familyInclusionData m).compresses
    (lamp_commutes_base m) (PresentedGroup.of v1Index) (mark m)
    (mark_eq_rootCommutator_sq m)
    (ScalingFamilyLinearWitness.scaling_mark_ne_one hm) (mark_sq m)
    (mark_central m)

/-- **Every member of the scaling family with `m ≥ 2` fails the manuscript's
genuine-corona CDE predicate.** -/
theorem scalingFamily_not_isCDEOperatorMF (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsCDEOperatorMF (MarkedGroup m) :=
  (scaling_centralSignCriterion m hm).2

/-- **Every member of the scaling family with `m ≥ 2` is not operator MF.** -/
theorem scalingFamily_not_isOperatorMF (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsOperatorMF (MarkedGroup m) := by
  rw [← isCDEOperatorMF_iff_isOperatorMF]
  exact scalingFamily_not_isCDEOperatorMF m hm

/-- Every proposition implying operator MF fails for the `m`-th group. -/
theorem scalingFamily_not_of_implies_isOperatorMF
    (m : ℕ) (hm : 2 ≤ m) (P : Prop)
    (hP : P → IsOperatorMF (MarkedGroup m)) : ¬ P :=
  not_of_implies_isOperatorMF (scalingFamily_not_isOperatorMF m hm) P hP

/-- The concrete reduced group C-star algebra of the `m`-th member admits no
faithful embedding into any norm-matrix C-star corona. -/
theorem scalingFamily_reducedGroupCStar_not_hasMFEmbedding (m : ℕ) (hm : 2 ≤ m) :
    ¬ HasMFEmbedding (ReducedGroupCStar (MarkedGroup m)) :=
  not_hasMFEmbedding_reducedGroupCStar_of_not_isGroupTheoreticMF
    (scalingFamily_not_isOperatorMF m hm)

/-- The concrete reduced group C-star algebra is not MF. -/
theorem scalingFamily_reducedGroupCStar_not_isMFAlgebra (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsMFAlgebra (ReducedGroupCStar (MarkedGroup m)) := by
  intro hMF
  exact scalingFamily_reducedGroupCStar_not_hasMFEmbedding m hm hMF.2

/-- The universe-relative maximal group C-star algebra is not MF. -/
theorem scalingFamily_maximalGroupCStar_not_isMFAlgebra (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsMFAlgebra (MaximalGroupCStar (MarkedGroup m)) :=
  maximalGroupCStar_not_isMFAlgebra_of_not_isOperatorMF (MarkedGroup m)
    (scalingFamily_not_isOperatorMF m hm)

/-- Every member with `m ≥ 2` fails every standard MF convention formalized
in the development, including PMatF, trace-free PPermF, trace-PMF, PFF, and
PPF.  The same package records failure of the embedding and MF-algebra
predicates for the universe-relative maximal model and the concrete reduced
group C-star algebra. -/
theorem scalingFamily_failsEveryStandardMFConvention
    (m : ℕ) (hm : 2 ≤ m) :
    FailsEveryStandardMFConvention (MarkedGroup m) :=
  failsEveryStandardMFConvention_of_not_isOperatorMF
    (scalingFamily_not_isOperatorMF m hm)

/-! ## Exact manuscript endpoint for the family -/

/-- **Unconditional manuscript Theorem A for the whole scaling family.**

For every scaling factor `m ≥ 2` the presented group with stable relations
`t vᵢ t⁻¹ = vᵢ^m` carries a nontrivial central involution that is killed by
every genuine matrix corona representation, and the group is not MF in any
of the formalized senses.  `m = 2` is the literal manuscript group. -/
theorem manuscriptTheoremFamily :
    ∀ (m : ℕ), 2 ≤ m →
    Group.IsFinitelyPresented (MarkedGroup m) ∧
      (mark m ≠ 1 ∧ mark m ^ 2 = 1 ∧ ∀ g : MarkedGroup m, Commute (mark m) g) ∧
      (∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →
        ∀ Theta : MarkedGroup m →*
          NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (d n)),
          Theta (mark m) = 1) ∧
      ¬ IsCDEOperatorMF (MarkedGroup m) ∧
      ¬ IsMFAlgebra (MaximalGroupCStar (MarkedGroup m)) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar (MarkedGroup m)) :=
  fun m hm ↦
    ⟨inferInstance,
      ⟨(cliffordSign_blackHole hm).2, mark_sq m, mark_central m⟩,
      scaling_mark_eq_one_in_unitaryCorona m,
      scalingFamily_not_isCDEOperatorMF m hm,
      scalingFamily_maximalGroupCStar_not_isMFAlgebra m hm,
      scalingFamily_reducedGroupCStar_not_isMFAlgebra m hm⟩

end

end ScalingFamilyEndpoint
end GroupApproximation
