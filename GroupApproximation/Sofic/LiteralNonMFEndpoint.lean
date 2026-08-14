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
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.MFDefinitions

/-!
# The literal eight-generator non-MF endpoint

This file is the sole unconditional endpoint for the exact eight-generator
presentation in the manuscript.  The premise-free property-`(T)` theorem for
the literal base is consumed directly from `LiteralBaseP13PropertyTBridge`;
there is no conditional compatibility surface.

The declarations follow the mathematical spine of the proof:

1. assemble the literal marked-compression datum;
2. identify the marked central involution as a squared compression defect;
3. place `{1, mark}` in the compression-defect normal closure;
4. annihilate it in every norm-matrix corona; and
5. combine that annihilation with the explicit Clifford witness.
-/

namespace GroupApproximation
namespace LiteralNonMFEndpoint

open LiteralNonMFPresentation
open ReducedGroupCStarTrace
open scoped commutatorElement

noncomputable section

/-! ## The literal marked-compression datum -/

/-- The exact marked-compression datum for the literal group.  Its
property-`(T)` field is discharged by the premise-free P13 bridge. -/
noncomputable def conceptualInclusionData :
    MarkedCompressionInclusionData Base MarkedGroup where
  iota := baseMap
  t := stable
  c := lamp
  a := PresentedGroup.of v1Index
  kazhdan := LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT
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

@[simp] theorem conceptualInclusionData_word :
    conceptualInclusionData.word = mark :=
  mark_eq_markedCompressionWord.symm

/-- The transported involution `d = t c t⁻¹`. -/
abbrev compressionRoot : MarkedGroup :=
  conceptualInclusionData.toKazhdanCompressionCore.transported

/-- The distinguished pointwise compression defect `u = [d,a]`. -/
abbrev compressionDefect : MarkedGroup :=
  ⁅compressionRoot, conceptualInclusionData.iota conceptualInclusionData.a⁆

/-! ## The algebraic box: `w = u²` -/

/-- The literal mark is the square of the distinguished compression defect. -/
theorem mark_eq_compressionDefect_sq : mark = compressionDefect ^ 2 := by
  have h := conceptualInclusionData.word_eq_compressionDefect_sq lamp_sq
  rw [conceptualInclusionData_word] at h
  exact h

/-- The square identity together with the Clifford realization: the square
of the compression defect is genuinely nontrivial. -/
theorem compressionDefect_sq_ne_one : compressionDefect ^ 2 ≠ 1 := by
  rw [← mark_eq_compressionDefect_sq]
  exact LiteralNonMFLinearWitness.literal_mark_ne_one

/-! ## Kazhdan pinning -/

/-- Every pointwise compression defect converges to the identity in
normalized Hilbert--Schmidt distance in every operator-norm almost
representation. -/
theorem kazhdanPinning (B : OpAlmostRepresentation MarkedGroup) :
    KazhdanCompressionCore.CompressionDefectsHSTrivial
      conceptualInclusionData.toKazhdanCompressionCore B :=
  conceptualInclusionData.toKazhdanCompressionCore.compressionDefects_hsTrivial B

/-- A separated negative corner for the literal mark contradicts Kazhdan
transport and the identity `mark = compressionDefect²`. -/
theorem negativeCorner_kazhdanTransport_contradiction
    (A : MarkedOpAlmostRepresentation MarkedGroup mark) : False := by
  rw [← conceptualInclusionData_word] at A
  exact KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation
    conceptualInclusionData A

/-! ## The explicit finite normal subgroup `{1, mark}` -/

/-- The literal two-point subgroup used in the finite-normal obstruction. -/
noncomputable def literalInvolutionSubgroup : Subgroup MarkedGroup :=
  centralInvolutionSubgroup mark mark_sq

@[simp] theorem mem_literalInvolutionSubgroup_iff (g : MarkedGroup) :
    g ∈ literalInvolutionSubgroup ↔ g = 1 ∨ g = mark :=
  Iff.rfl

@[simp] theorem coe_literalInvolutionSubgroup :
    (literalInvolutionSubgroup : Set MarkedGroup) = {1, mark} :=
  coe_centralInvolutionSubgroup mark mark_sq

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

/-- The explicit subgroup `{1, mark}` belongs to the normal closure of the
pinned compression defects. -/
theorem literalInvolutionSubgroup_le_defectNormal :
    literalInvolutionSubgroup ≤
      conceptualInclusionData.toKazhdanCompressionCore.defectNormal := by
  rw [literalInvolutionSubgroup,
    centralInvolutionSubgroup_le_iff_mem mark mark_sq]
  rw [← conceptualInclusionData_word]
  exact conceptualInclusionData.word_mem_compressionDefectNormal

/-! ## Corona annihilation -/

/-- Every homomorphism into the unitary group of a genuine positive-size
norm-matrix C-star corona kills `{1, mark}`. -/
theorem literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      literalInvolutionSubgroup ≤ rho.ker := by
  exact KazhdanCompressionCore.finiteNormal_le_normMatrixCStarCoronaKernel
    conceptualInclusionData.toKazhdanCompressionCore
    literalInvolutionSubgroup literalInvolutionSubgroup_le_defectNormal X hX

/-- Every homomorphism into every positive-size unitary-sequence norm corona
kills `{1, mark}`. -/
theorem literalInvolutionSubgroup_le_normMatrixCoronaKernel
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
    literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel
      X hX (kappa.comp rho) hf
  apply MonoidHom.mem_ker.mpr
  apply (normMatrixCoronaUnitaryEquiv X).injective
  change kappa (rho f) = kappa 1
  have hkappa : kappa (rho f) = 1 := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      MonoidHom.mem_ker.mp hactual
  rw [hkappa, map_one]

/-- Every genuine positive-size norm-matrix C-star-corona representation
maps the literal mark to the identity. -/
theorem literal_mark_eq_one_in_normMatrixCStarCorona
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      rho mark = 1 := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  exact MonoidHom.mem_ker.mp
    (literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel
      X hX rho mark_mem_literalInvolutionSubgroup)

/-- The genuine C-star-corona statement in the manuscript's literal natural
matrix coordinates. -/
theorem literal_mark_eq_one_in_CStarCorona
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      rho mark = 1 := by
  simpa using literal_mark_eq_one_in_normMatrixCStarCorona
    (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd)

/-- The unitary-sequence-corona clause of the printed theorem, in literal
natural-number dimensions. -/
theorem literal_mark_eq_one_in_unitaryCorona
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (Theta : MarkedGroup →*
      NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (d n))) :
    Theta mark = 1 := by
  exact MonoidHom.mem_ker.mp
    (literalInvolutionSubgroup_le_normMatrixCoronaKernel
      (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd) Theta
      mark_mem_literalInvolutionSubgroup)

/-- The literal mark belongs to the MF radical exactly as printed, defined
through genuine natural-dimension C-star coronas. -/
theorem literal_mark_mem_manuscriptCoronaMFResidual :
    mark ∈ manuscriptCoronaMFResidual MarkedGroup := by
  exact (mem_manuscriptCoronaMFResidual_iff (G := MarkedGroup)).2
    literal_mark_eq_one_in_CStarCorona

/-- The mark also belongs to the basis-free unitary-sequence MF residual. -/
theorem literal_mark_normMFInvisible : NormMFInvisible mark :=
  KazhdanCompressionCore.finiteNormal_le_normMFResidual
    conceptualInclusionData.toKazhdanCompressionCore
    literalInvolutionSubgroup literalInvolutionSubgroup_le_defectNormal
    mark_mem_literalInvolutionSubgroup

/-! ## Premise-free MF and C-star consequences -/

/-- The corona obstruction and the Clifford detector in one statement. -/
theorem cliffordSign_blackHole :
    NormMFInvisible mark ∧ mark ≠ 1 :=
  ⟨literal_mark_normMFInvisible,
    LiteralNonMFLinearWitness.literal_mark_ne_one⟩

/-- The literal eight-generator group is not operator MF. -/
theorem literal_not_isOperatorMF : ¬ IsOperatorMF MarkedGroup :=
  MarkedCompressionInclusionData.not_isOperatorMF_of_mem_finiteNormal
    conceptualInclusionData literalInvolutionSubgroup
    literalInvolutionSubgroup_le_defectNormal
    (by
      rw [conceptualInclusionData_word]
      exact mark_mem_literalInvolutionSubgroup)
    (by
      rw [conceptualInclusionData_word]
      exact LiteralNonMFLinearWitness.literal_mark_ne_one)

/-- The same conclusion in the manuscript's genuine-corona CDE predicate. -/
theorem literal_not_isCDEOperatorMF : ¬ IsCDEOperatorMF MarkedGroup := by
  rw [isCDEOperatorMF_iff_isOperatorMF]
  exact literal_not_isOperatorMF

/-- The literal group fails every equivalent MF formulation and every
stronger MF variant formalized in this development. -/
theorem literal_failsAllFormalizedMFVariants :
    FailsAllFormalizedMFVariants MarkedGroup :=
  failsAllFormalizedMFVariants_of_not_isGroupTheoreticMF
    literal_not_isOperatorMF

/-- The concrete reduced group C-star algebra admits no faithful embedding
into any norm-matrix C-star corona. -/
theorem literal_reducedGroupCStar_not_hasMFEmbedding :
    ¬ HasMFEmbedding (ReducedGroupCStar MarkedGroup) :=
  not_hasMFEmbedding_reducedGroupCStar_of_not_isGroupTheoreticMF
    literal_not_isOperatorMF

/-- The concrete reduced group C-star algebra is not MF. -/
theorem literal_reducedGroupCStar_not_isMFAlgebra :
    ¬ IsMFAlgebra (ReducedGroupCStar MarkedGroup) := by
  intro hMF
  exact literal_reducedGroupCStar_not_hasMFEmbedding hMF.2

/-- The universe-relative maximal group C-star algebra admits no faithful
embedding into any norm-matrix C-star corona. -/
theorem literal_maximalGroupCStar_not_hasMFEmbedding :
    ¬ HasMFEmbedding (MaximalGroupCStar MarkedGroup) :=
  maximalGroupCStar_not_hasMFEmbedding_of_not_isOperatorMF MarkedGroup
    literal_not_isOperatorMF

/-- The universe-relative maximal group C-star algebra is not MF. -/
theorem literal_maximalGroupCStar_not_isMFAlgebra :
    ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) :=
  maximalGroupCStar_not_isMFAlgebra_of_not_isOperatorMF MarkedGroup
    literal_not_isOperatorMF

/-! ## Exact manuscript endpoints -/

/-- **Unconditional manuscript Theorem A.** -/
theorem manuscriptTheoremA :
    (mark ≠ 1 ∧ mark ^ 2 = 1 ∧ ∀ g : MarkedGroup, Commute mark g) ∧
      (∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →
        ∀ Theta : MarkedGroup →*
          NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (d n)),
          Theta mark = 1) ∧
      ¬ IsCDEOperatorMF MarkedGroup ∧
      ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar MarkedGroup) :=
  ⟨⟨cliffordSign_blackHole.2, mark_sq, mark_central⟩,
    literal_mark_eq_one_in_unitaryCorona,
    literal_not_isCDEOperatorMF,
    literal_maximalGroupCStar_not_isMFAlgebra,
    literal_reducedGroupCStar_not_isMFAlgebra⟩

/-- **Unconditional manuscript Theorem D.**

The concrete reduced group C-star algebra is separable, carries a faithful
tracial state, is stably finite in every nonempty finite matrix
amplification, and is not MF. -/
theorem manuscriptTheoremD :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar MarkedGroup) ∧
      Nonempty (FaithfulTracialState (ReducedGroupCStar MarkedGroup)) ∧
      (∀ (I : Type) [Fintype I] [DecidableEq I], Nonempty I →
        ∀ v : CStarMatrix I I (ReducedGroupCStar MarkedGroup),
          star v * v = 1 → v * star v = 1) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar MarkedGroup) := by
  refine ⟨reducedGroupCStar_separableSpace MarkedGroup,
    ⟨canonicalFaithfulTracialState MarkedGroup⟩, ?_,
    literal_reducedGroupCStar_not_isMFAlgebra⟩
  intro I _ _ hI v hv
  exact (canonicalFaithfulTracialState MarkedGroup).matrix_mul_star_eq_one_of_star_mul_eq_one
    I hI hv

end

end LiteralNonMFEndpoint
end GroupApproximation
