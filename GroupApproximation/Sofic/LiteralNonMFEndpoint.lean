import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.MFDefinitions
import GroupApproximation.Analysis.MaximalGroupCStar

/-!
# The literal eight-generator endpoint assembly

This file assembles the exact group-theoretic and analytic interfaces for the
eight-generator presentation in `LiteralNonMFPresentation`, retaining the
single explicit property-`(T)` premise until the proof-carrying rational P13
Hodge certificate has been fully checked and integrated.

The suffixed declarations retain the useful abstract interface accepting an
arbitrary proof of base property `(T)`; the unsuffixed declarations at the end
instantiate it with the exact certificate and give:

* marked-compression inclusion data for the literal presentation;
* the explicit finite normal subgroup `{1, mark}` inside the compression
  defect;
* universal annihilation of that subgroup by homomorphisms into the unitary
  group of every genuine norm-matrix C-star corona; and
* failure of both the internal operator-MF predicate and the literal CDE
  predicate for the displayed group.

-/

namespace GroupApproximation
namespace LiteralNonMFEndpoint

open LiteralNonMFPresentation

noncomputable section

/-- The finite index type underlying the manuscript's literal matrix algebra
`M_d(ℂ)`.  Keeping this wrapper here lets the final theorem quantify over
natural-number dimensions exactly as the printed statement does. -/
abbrev naturalMatrixModel (d : ℕ) : FiniteModel where
  carrier := Fin d
  fintype := inferInstance
  decidableEq := inferInstance

@[simp] theorem card_naturalMatrixModel (d : ℕ) :
    Fintype.card (naturalMatrixModel d) = d := by
  simp [naturalMatrixModel]

/-! ## The literal marked-compression data -/

/-- The exact marked-compression datum carried by the literal presentation,
conditional only on property `(T)` of its literal base. -/
noncomputable def inclusionDataOfHasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    MarkedCompressionInclusionData Base MarkedGroup where
  iota := baseMap
  t := stable
  c := lamp
  a := PresentedGroup.of v1Index
  kazhdan := hT
  compresses gamma := by
    obtain ⟨delta, hdelta⟩ := stable_conjugates_base_into_base gamma
    exact ⟨delta, hdelta.symm⟩
  comm_c := lamp_commutes_base
  word_sq := by
    rw [← mark_eq_markedCompressionWord]
    exact mark_sq
  word_central g := by
    rw [← mark_eq_markedCompressionWord]
    exact mark_central g

@[simp] theorem inclusionDataOfHasKazhdanPropertyT_word
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    (inclusionDataOfHasKazhdanPropertyT hT).word = mark := by
  exact mark_eq_markedCompressionWord.symm

/-! ## The explicit finite normal subgroup `{1, mark}` -/

/-- The literal two-point subgroup used in the finite-normal obstruction. -/
noncomputable def literalInvolutionSubgroup : Subgroup MarkedGroup :=
  centralInvolutionSubgroup mark mark_sq

@[simp] theorem mem_literalInvolutionSubgroup_iff (g : MarkedGroup) :
    g ∈ literalInvolutionSubgroup ↔ g = 1 ∨ g = mark :=
  Iff.rfl

@[simp] theorem coe_literalInvolutionSubgroup :
    (literalInvolutionSubgroup : Set MarkedGroup) = {1, mark} := by
  exact coe_centralInvolutionSubgroup mark mark_sq

@[simp] theorem mark_mem_literalInvolutionSubgroup :
    mark ∈ literalInvolutionSubgroup :=
  involution_mem_centralInvolutionSubgroup mark mark_sq

noncomputable instance literalInvolutionSubgroup_finite :
    Finite literalInvolutionSubgroup :=
  centralInvolutionSubgroup_finite mark mark_sq

instance literalInvolutionSubgroup_normal :
    literalInvolutionSubgroup.Normal :=
  centralInvolutionSubgroup_normal mark mark_sq mark_central

instance literalInvolutionSubgroup_nontrivial :
    Nontrivial literalInvolutionSubgroup :=
  centralInvolutionSubgroup_nontrivial mark mark_sq
    LiteralNonMFLinearWitness.literal_mark_ne_one

/-- The explicit subgroup `{1, mark}` lies in the compression-defect normal
closure.  The proof uses the literal marked word, rather than replacing it by
an abstract finite normal subgroup. -/
theorem literalInvolutionSubgroup_le_defectNormal_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    literalInvolutionSubgroup ≤
      (inclusionDataOfHasKazhdanPropertyT hT).toKazhdanCompressionCore.defectNormal := by
  rw [literalInvolutionSubgroup,
    centralInvolutionSubgroup_le_iff_mem mark mark_sq]
  rw [← inclusionDataOfHasKazhdanPropertyT_word hT]
  exact
    (inclusionDataOfHasKazhdanPropertyT hT).word_mem_compressionDefectNormal

/-! ## Actual C-star-corona and MF conclusions -/

/-- Every homomorphism from the literal group into the unitary group of a
genuine positive-size norm-matrix C-star corona kills the explicit subgroup
`{1, mark}`. -/
theorem literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      literalInvolutionSubgroup ≤ rho.ker := by
  exact
    KazhdanCompressionCore.finiteNormal_le_normMatrixCStarCoronaKernel
      (inclusionDataOfHasKazhdanPropertyT hT).toKazhdanCompressionCore
      literalInvolutionSubgroup
      (literalInvolutionSubgroup_le_defectNormal_of_hasKazhdanPropertyT hT)
      X hX

/-- Every homomorphism from the literal group into every positive-size
unitary-sequence norm corona kills the explicit subgroup `{1, mark}`.

This proof follows the manuscript literally: compose with the canonical
polar-correction equivalence into the unitary group of the genuine C-star
corona, apply the preceding C-star-corona theorem, and use injectivity of the
equivalence. -/
theorem literalInvolutionSubgroup_le_normMatrixCoronaKernel_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : MarkedGroup →* NormMatrixCoronaUnitary X) :
    literalInvolutionSubgroup ≤ rho.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  let kappa : NormMatrixCoronaUnitary X →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (normMatrixCoronaUnitaryEquiv X).toMonoidHom
  intro f hf
  have hactual : f ∈ (kappa.comp rho).ker :=
    literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel_of_hasKazhdanPropertyT
      hT X hX (kappa.comp rho) hf
  apply MonoidHom.mem_ker.mpr
  apply (normMatrixCoronaUnitaryEquiv X).injective
  change kappa (rho f) = kappa 1
  have hkappa : kappa (rho f) = 1 := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      MonoidHom.mem_ker.mp hactual
  rw [hkappa, map_one]

/-- The unitary-sequence-corona clause of the printed theorem, with literal
natural-number matrix dimensions. -/
theorem literal_mark_eq_one_in_unitaryCorona_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (Theta : MarkedGroup →*
      NormMatrixCoronaUnitary (fun n ↦ naturalMatrixModel (d n))) :
    Theta mark = 1 := by
  have hker : mark ∈ Theta.ker :=
    literalInvolutionSubgroup_le_normMatrixCoronaKernel_of_hasKazhdanPropertyT
      hT (fun n ↦ naturalMatrixModel (d n)) (by simpa using hd) Theta
      mark_mem_literalInvolutionSubgroup
  exact MonoidHom.mem_ker.mp hker

/-- Every homomorphism from the literal group into the unitary group of a
genuine positive-size norm-matrix C-star corona maps the literal mark to the
identity. -/
theorem literal_mark_eq_one_in_normMatrixCStarCorona_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      rho mark = 1 := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  exact MonoidHom.mem_ker.mp
    (literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel_of_hasKazhdanPropertyT
      hT X hX rho mark_mem_literalInvolutionSubgroup)

/-- The genuine C-star-corona version with literal natural-number matrix
dimensions. -/
theorem literal_mark_eq_one_in_CStarCorona_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    letI : ∀ n, Nonempty (naturalMatrixModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    ∀ Theta : MarkedGroup →*
      unitary (NormMatrixCStarCorona
        (fun n ↦ naturalMatrixModel (d n))),
      Theta mark = 1 := by
  simpa using
    literal_mark_eq_one_in_normMatrixCStarCorona_of_hasKazhdanPropertyT
      hT (fun n ↦ naturalMatrixModel (d n)) (by simpa using hd)

/-- The literal mark lies in the universal operator-norm MF residual. -/
theorem literal_mark_normMFInvisible_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    NormMFInvisible mark :=
  KazhdanCompressionCore.finiteNormal_le_normMFResidual
    (inclusionDataOfHasKazhdanPropertyT hT).toKazhdanCompressionCore
    literalInvolutionSubgroup
    (literalInvolutionSubgroup_le_defectNormal_of_hasKazhdanPropertyT hT)
    mark_mem_literalInvolutionSubgroup

/-- Conditional boundary for the literal operator-MF conclusion.  The
hypothesis is exactly the one theorem still being discharged upstream. -/
theorem literal_not_isOperatorMF_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsOperatorMF MarkedGroup :=
  MarkedCompressionInclusionData.not_isOperatorMF_of_mem_finiteNormal
    (inclusionDataOfHasKazhdanPropertyT hT) literalInvolutionSubgroup
    (literalInvolutionSubgroup_le_defectNormal_of_hasKazhdanPropertyT hT)
    (by
      rw [inclusionDataOfHasKazhdanPropertyT_word]
      exact mark_mem_literalInvolutionSubgroup)
    (by
      rw [inclusionDataOfHasKazhdanPropertyT_word]
      exact LiteralNonMFLinearWitness.literal_mark_ne_one)

/-- The same conditional boundary stated using the literal CDE definition
with the genuine C-star corona and strictly increasing positive dimensions. -/
theorem literal_not_isCDEOperatorMF_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsCDEOperatorMF MarkedGroup := by
  rw [isCDEOperatorMF_iff_isOperatorMF]
  exact literal_not_isOperatorMF_of_hasKazhdanPropertyT hT

/-- The concrete reduced group C-star algebra admits no faithful embedding
into any norm-matrix C-star corona.  This is stronger than failure of the MF
predicate because it does not use its separability conjunct. -/
theorem literal_reducedGroupCStar_not_hasMFEmbedding_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ HasMFEmbedding (ReducedGroupCStarTrace.ReducedGroupCStar MarkedGroup) :=
  not_hasMFEmbedding_reducedGroupCStar_of_not_isGroupTheoreticMF
    (literal_not_isOperatorMF_of_hasKazhdanPropertyT hT)

/-- Consequently, the concrete reduced group C-star algebra of the literal
group is not an MF C-star algebra. -/
theorem literal_not_isReducedGroupCStarMF_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsReducedGroupCStarMF MarkedGroup := by
  intro hMF
  exact literal_reducedGroupCStar_not_hasMFEmbedding_of_hasKazhdanPropertyT
    hT hMF.2

/-- The canonical maximal group C-star algebra of the literal group admits
no faithful embedding into a norm-matrix C-star corona. -/
theorem literal_maximalGroupCStar_not_hasMFEmbedding_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ HasMFEmbedding (MaximalGroupCStar MarkedGroup) :=
  maximalGroupCStar_not_hasMFEmbedding_of_not_isOperatorMF MarkedGroup
    (literal_not_isOperatorMF_of_hasKazhdanPropertyT hT)

/-- Consequently, the canonical maximal group C-star algebra of the literal
group is not an MF C-star algebra. -/
theorem literal_maximalGroupCStar_not_isMFAlgebra_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) :=
  maximalGroupCStar_not_isMFAlgebra_of_not_isOperatorMF MarkedGroup
    (literal_not_isOperatorMF_of_hasKazhdanPropertyT hT)

/-- Manuscript Theorem A for the literal presentation, still carrying the
single honest property-`(T)` boundary.  The theorem records the literal
central involution, the printed unitary-sequence-corona conclusion with
natural-number matrix dimensions, failure of the group MF property, and the
object-level maximal and reduced group C-star consequences. -/
theorem manuscriptTheoremA_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    (mark ≠ 1 ∧ mark ^ 2 = 1 ∧ ∀ g : MarkedGroup, Commute mark g) ∧
      (∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →
        ∀ Theta : MarkedGroup →*
          NormMatrixCoronaUnitary (fun n ↦ naturalMatrixModel (d n)),
          Theta mark = 1) ∧
      ¬ IsOperatorMF MarkedGroup ∧
      ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) ∧
      ¬ IsReducedGroupCStarMF MarkedGroup := by
  refine ⟨⟨LiteralNonMFLinearWitness.literal_mark_ne_one, mark_sq,
    mark_central⟩, ?_, literal_not_isOperatorMF_of_hasKazhdanPropertyT hT,
    literal_maximalGroupCStar_not_isMFAlgebra_of_hasKazhdanPropertyT hT,
    literal_not_isReducedGroupCStarMF_of_hasKazhdanPropertyT hT⟩
  intro d hd Theta
  exact literal_mark_eq_one_in_unitaryCorona_of_hasKazhdanPropertyT
    hT d hd Theta

end

end LiteralNonMFEndpoint
end GroupApproximation
