import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Analysis.UltraproductRigidityRoute
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.KazhdanSignCriterion
import GroupApproximation.Sofic.LiteralNonMFCoreEndpoint
import GroupApproximation.Sofic.MFRepresentationVariants
import GroupApproximation.Sofic.ManuscriptCentralSignCriterion
import GroupApproximation.Sofic.PrintedCentralSignCriterion
import GroupApproximation.Sofic.PrintedNegativeCornerKill

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

/-- The transported involution `d = t c t⁻¹`. -/
abbrev compressionRoot : MarkedGroup :=
  inclusionData.toKazhdanCompressionCore.transported

/-- The distinguished pointwise compression defect `u = [d,a]`. -/
abbrev compressionDefect : MarkedGroup :=
  ⁅compressionRoot, inclusionData.iota inclusionData.a⁆

/-! ## The algebraic box: `w = u²` -/

/-- The literal mark is the square of the distinguished compression defect. -/
theorem mark_eq_compressionDefect_sq : mark = compressionDefect ^ 2 := by
  have h := inclusionData.word_eq_compressionDefect_sq lamp_sq
  rw [inclusionData_word] at h
  exact h

/-- The same identity in the manuscript's own notation: the mark is the
square of the commutator of the transported root `d = t c t⁻¹` with `ι(v₁)`. -/
theorem mark_eq_rootCommutator_sq :
    mark = ⁅stable * lamp * stable⁻¹, baseMap (PresentedGroup.of v1Index)⁆ ^ 2 :=
  mark_eq_compressionDefect_sq

/-- The square identity together with the Clifford realization: the square
of the compression defect is genuinely nontrivial. -/
theorem compressionDefect_sq_ne_one : compressionDefect ^ 2 ≠ 1 := by
  rw [← mark_eq_compressionDefect_sq]
  exact LiteralNonMFLinearWitness.literal_mark_ne_one

/-! ## Kazhdan pinning -/

/-- Every pointwise compression defect converges to the identity in
normalized Hilbert--Schmidt distance in every operator-norm almost
representation.

**By the printed route.**  The transport step is
`\ref{thm:kazhdan-transport}` itself, through
`UltraproductRigidityRoute.compressionDefects_hsTrivial_literal` and
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`, which is the proof
`\ref{thm:criterion}` prints: "apply Theorem 3.1 with `x_n = U_{c,n}` to put
the lifts of `ĉ = t c t⁻¹` in the commutant".  It used to travel
`KazhdanCompressionCore.compressionDefects_hsTrivial`, whose one transport
step is the finite-stage corner argument instead; that route is unchanged and
still proves the same statement, and the corner bookkeeping below the
transport is shared by both. -/
theorem kazhdanPinning (B : OpAlmostRepresentation MarkedGroup) :
    KazhdanCompressionCore.CompressionDefectsHSTrivial
      inclusionData.toKazhdanCompressionCore B :=
  UltraproductRigidityRoute.compressionDefects_hsTrivial_literal
    inclusionData.toKazhdanCompressionCore B

/-- A separated negative corner for the literal mark contradicts Kazhdan
transport and the identity `mark = compressionDefect²`.

**By the printed route.**  The transport half is the pinning above, so this
declaration and `kazhdanPinning` travel the same step,
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`, which is
`\ref{thm:kazhdan-transport}` by the printed §3 ultraproduct proof.  What the
negative corner adds is the printed "hence `w ~₂ 1`": the mark is the square of
the pinned compression defect, and squaring at most quadruples the normalized
Hilbert--Schmidt displacement.  It used to travel
`KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation`, whose transport
step is the finite-stage corner argument instead; that route is unchanged and
still proves the same statement. -/
theorem negativeCorner_kazhdanTransport_contradiction :
    ∀ (_A : MarkedOpAlmostRepresentation MarkedGroup mark), False := by
  intro A
  rw [← inclusionData_word] at A
  exact PrintedNegativeCornerKill.false_of_markedOpAlmostRepresentation_printed
    inclusionData lamp_sq A

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
      inclusionData.toKazhdanCompressionCore.defectNormal := by
  rw [literalInvolutionSubgroup,
    centralInvolutionSubgroup_le_iff_mem mark mark_sq]
  rw [← inclusionData_word]
  exact inclusionData.word_mem_compressionDefectNormal

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
    inclusionData.toKazhdanCompressionCore
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
maps the literal mark to the identity.

This is the central-sign criterion applied to the literal datum: the mark is
the square of the distinguished pointwise compression defect
(`mark_eq_compressionDefect_sq`), and it is a central involution. -/
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
    (KazhdanCompressionCore.defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel
      inclusionData.toKazhdanCompressionCore inclusionData.a mark
      mark_eq_compressionDefect_sq mark_sq mark_central X hX rho)

/-! ## The central-sign criterion, applied

The manuscript proves Theorem A by *applying* the central-sign criterion to
the literal datum.  The next declaration is that application, verbatim: the
closed proposition `ManuscriptCentralSignCriterion` is instantiated at
`Γ = Base`, `E = MarkedGroup`, `ι = baseMap`, `t = stable`, `c = lamp`,
`a = v₁`, and `z = mark`, with `mark = [t c t⁻¹, ι(v₁)]²` supplied by
`mark_eq_compressionDefect_sq` and `mark ≠ 1` by the Clifford witness.  Both
mathematical clauses of Theorem A are read off from its conclusion. -/

/-- **The central-sign criterion at the literal datum.**

**By the printed route.**  The criterion instantiated here is
`PrintedCentralSign.manuscriptCentralSignCriterionPrinted`, whose one transport
step is `\ref{thm:kazhdan-transport}` by the printed §3 ultraproduct proof.  It
used to be `KazhdanCompressionCore.manuscriptCentralSignCriterion`, which
inhabits the *same* closed proposition through the finite-stage corner; that
route is unchanged and still proves the same statement.  What is instantiated,
and at which data, is untouched -- the swap is the choice of inhabitant and
nothing else, which is why the rows that grade this application do not move. -/
theorem literal_centralSignCriterion :
    (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho mark = 1) ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  -- Two universe levels: the ambient group's, then the property-`(T)`
  -- Hilbert-space universe.  Both are `0` for the literal marked group.
  GroupApproximation.PrintedCentralSign.manuscriptCentralSignCriterionPrinted.{0, 0}
    (Γ := Base) (E := MarkedGroup)
    LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT.2
    baseMap stable lamp inclusionData.compresses lamp_commutes_base
    (PresentedGroup.of v1Index) mark mark_eq_rootCommutator_sq
    LiteralNonMFLinearWitness.literal_mark_ne_one mark_sq mark_central

/-- The genuine C-star-corona statement in the manuscript's literal natural
matrix coordinates.  This is the first clause of the criterion. -/
theorem literal_mark_eq_one_in_CStarCorona
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      rho mark = 1 :=
  literal_centralSignCriterion.1 d hd

/-- The unitary-sequence-corona clause of the printed theorem, in literal
natural-number dimensions.

This is part (2) of the literal verification of Theorem~`\ref{thm:A}`, by its
printed argument: "let
`Θ : E → 𝒰cor((d_n))` be given and pass to the corona representation
`κ_{(d_n)} ∘ Θ : E → 𝒰(𝒬)` of Lemma~`\ref{lem:unitarycorona}`.  Apply the
central-sign criterion (Theorem~`\ref{thm:sign-criterion}`) ... The criterion
therefore sends `w` to the identity under every corona representation of `E`.
Since `κ_{(d_n)}` is injective, `Θ(w) = 1`."

So the criterion is applied to the genuine C-star corona and transported back
across `κ`, rather than the unitary-sequence statement being obtained
independently from the finite-normal kernel theorem. -/
theorem literal_mark_eq_one_in_unitaryCorona
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (Theta : MarkedGroup →*
      NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (d n))) :
    Theta mark = 1 := by
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  let kappa : NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (d n)) →*
      unitary (NormMatrixCStarCorona (fun n ↦ naturalFiniteModel (d n))) :=
    (normMatrixCoronaUnitaryEquiv (fun n ↦ naturalFiniteModel (d n))).toMonoidHom
  have hkappa : kappa (Theta mark) = 1 := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      literal_mark_eq_one_in_CStarCorona d hd (kappa.comp Theta)
  apply (normMatrixCoronaUnitaryEquiv
    (fun n ↦ naturalFiniteModel (d n))).injective
  change kappa (Theta mark) = kappa 1
  rw [hkappa, map_one]

/-- The literal mark belongs to the MF radical exactly as printed, defined
through genuine natural-dimension C-star coronas. -/
theorem literal_mark_mem_manuscriptCoronaMFResidual :
    mark ∈ manuscriptCoronaMFResidual MarkedGroup := by
  exact (mem_manuscriptCoronaMFResidual_iff (G := MarkedGroup)).2
    literal_mark_eq_one_in_CStarCorona

/-! ## Premise-free MF and C-star consequences -/

/-- The corona obstruction and the Clifford detector in one statement. -/
theorem cliffordSign_blackHole :
    NormMFInvisible mark ∧ mark ≠ 1 :=
  ⟨literal_mark_normMFInvisible,
    LiteralNonMFLinearWitness.literal_mark_ne_one⟩

/-- The literal eight-generator group fails the manuscript's genuine-corona
CDE predicate.  This is the second clause of the central-sign criterion at the
literal datum. -/
theorem literal_not_isCDEOperatorMF : ¬ IsCDEOperatorMF MarkedGroup :=
  literal_centralSignCriterion.2

/-- The literal eight-generator group is not operator MF. -/
theorem literal_not_isOperatorMF : ¬ IsOperatorMF MarkedGroup := by
  rw [← isCDEOperatorMF_iff_isOperatorMF]
  exact literal_not_isCDEOperatorMF

/-- Every proposition implying operator MF fails for the literal group. -/
theorem literal_not_of_implies_isOperatorMF
    (P : Prop) (hP : P → IsOperatorMF MarkedGroup) : ¬ P :=
  not_of_implies_isOperatorMF literal_not_isOperatorMF P hP

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

/-- The literal group fails every standard MF convention formalized in the
development, including PMatF, trace-free PPermF, trace-PMF, PFF, and PPF.
The same package records failure of the embedding and MF-algebra predicates
for the universe-relative maximal model and the concrete reduced group
C-star algebra. -/
theorem literal_failsEveryStandardMFConvention :
    FailsEveryStandardMFConvention MarkedGroup :=
  failsEveryStandardMFConvention_of_not_isOperatorMF
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
