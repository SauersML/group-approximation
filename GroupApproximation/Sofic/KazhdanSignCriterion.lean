import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.Type0Transfer
import GroupApproximation.Kazhdan.KazhdanUniverse

/-!
# The one-sign Kazhdan-compression criterion

This is the shortest reader-facing form of the operator-MF obstruction.
The analytic theorem says that every finite normal subgroup in the
Kazhdan-compression defect is invisible in every norm-matrix corona.  For the
Clifford construction one needs only its two-element special case: a
nontrivial central involution which is the square of one pointwise compression
defect rules out operator MF.
-/

namespace GroupApproximation
namespace KazhdanCompressionCore

open scoped commutatorElement

universe u w

/-! The auxiliary theorems below stay at `Type 0`, because the finite-normal
corner machinery they call is written there.  The closed proposition and the
advertised theorem do not: `thm:sign-criterion` says "let `H` be a countable
group", with no universe, so the ambient group is quantified at `Type u` and the
theorem is proved by descending to a `Type 0` model
(`Sofic.Type0Transfer.exists_type0_model`).  Nothing analytic is redone and no
hypothesis is added: countability is already printed, and it is exactly what the
descent consumes. -/

variable {Γ E : Type} [Group Γ] [Group E]

/-- The manuscript's central-sign criterion as one closed proposition.  All
groups, structure, and hypotheses are quantified inside the sentence, leaving
the advertised theorem with an empty declaration telescope.  The ambient group
ranges over every universe, as the manuscript's "countable group" does. -/
def ManuscriptCentralSignCriterion : Prop :=
  ∀ {Γ : Type} {E : Type u} [Group Γ] [Group E] [Countable E]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* E) (t c : E)
    (hcompresses : ∀ γ : Γ, ∃ δ : Γ,
      t * iota γ * t⁻¹ = iota δ)
    (hcomm : ∀ γ : Γ, Commute c (iota γ))
    (a : Γ) (z : E)
    (hz : z = ⁅t * c * t⁻¹, iota a⁆ ^ 2)
    (hz_ne : z ≠ 1) (hz_sq : z ^ 2 = 1)
    (hz_central : ∀ g : E, Commute z g),
    (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ rho : E →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho z = 1) ∧
      ¬ IsCDEOperatorMF E

/-- A central involution in the Kazhdan-compression defect is killed by every
homomorphism to every genuine positive-size norm-matrix C-star corona.  This
is the element-valued, reader-facing form of the finite-normal obstruction. -/
theorem centralInvolution_mem_normMatrixCStarCoronaKernel
    [Countable E] (C : KazhdanCompressionCore Γ E) (z : E)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (hz_defect : z ∈ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      z ∈ rho.ker := by
  let F : Subgroup E := centralInvolutionSubgroup z hz_sq
  letI : Finite F := centralInvolutionSubgroup_finite z hz_sq
  letI : F.Normal := centralInvolutionSubgroup_normal z hz_sq hz_central
  intro rho
  have hF : F ≤ C.defectNormal :=
    (centralInvolutionSubgroup_le_iff_mem z hz_sq C.defectNormal).mpr
      hz_defect
  exact C.finiteNormal_le_normMatrixCStarCoronaKernel F hF X hX rho
    (involution_mem_centralInvolutionSubgroup z hz_sq)

/-- The unitary-sequence form of the same annihilation: a central involution
in the Kazhdan-compression defect is killed by every homomorphism into every
positive-size unitary-sequence norm-matrix corona. -/
theorem centralInvolution_mem_normMatrixCoronaKernel
    [Countable E] (C : KazhdanCompressionCore Γ E) (z : E)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (hz_defect : z ∈ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : E →* NormMatrixCoronaUnitary X) :
    z ∈ rho.ker := by
  let F : Subgroup E := centralInvolutionSubgroup z hz_sq
  letI : Finite F := centralInvolutionSubgroup_finite z hz_sq
  letI : F.Normal := centralInvolutionSubgroup_normal z hz_sq hz_central
  have hF : F ≤ C.defectNormal :=
    (centralInvolutionSubgroup_le_iff_mem z hz_sq C.defectNormal).mpr
      hz_defect
  exact C.finiteNormal_le_normMatrixCoronaKernel F hF X hX rho
    (involution_mem_centralInvolutionSubgroup z hz_sq)

/-- The residual form of the same annihilation: a central involution in the
Kazhdan-compression defect is invisible to every operator-norm matrix
approximation. -/
theorem centralInvolution_normMFInvisible
    [Countable E] (C : KazhdanCompressionCore Γ E) (z : E)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (hz_defect : z ∈ C.defectNormal) :
    NormMFInvisible z := by
  let F : Subgroup E := centralInvolutionSubgroup z hz_sq
  letI : Finite F := centralInvolutionSubgroup_finite z hz_sq
  letI : F.Normal := centralInvolutionSubgroup_normal z hz_sq hz_central
  have hF : F ≤ C.defectNormal :=
    (centralInvolutionSubgroup_le_iff_mem z hz_sq C.defectNormal).mpr
      hz_defect
  exact C.finiteNormal_le_normMFResidual F hF
    (involution_mem_centralInvolutionSubgroup z hz_sq)

/-- If the square of one pointwise compression defect is a central
involution, every genuine norm-matrix-corona representation kills it. -/
theorem defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel
    [Countable E] (C : KazhdanCompressionCore Γ E) (a : Γ) (z : E)
    (hz : z = ⁅C.transported, C.iota a⁆ ^ 2)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      z ∈ rho.ker := by
  have hz_defect : z ∈ C.defectNormal := by
    rw [hz]
    exact C.defectNormal.pow_mem (C.defect_mem_defectNormal a) 2
  exact C.centralInvolution_mem_normMatrixCStarCoronaKernel
    z hz_sq hz_central hz_defect X hX

/-- The unitary-sequence form of the defect-square criterion. -/
theorem defectSquare_centralInvolution_mem_normMatrixCoronaKernel
    [Countable E] (C : KazhdanCompressionCore Γ E) (a : Γ) (z : E)
    (hz : z = ⁅C.transported, C.iota a⁆ ^ 2)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : E →* NormMatrixCoronaUnitary X) :
    z ∈ rho.ker :=
  C.centralInvolution_mem_normMatrixCoronaKernel z hz_sq hz_central
    (by
      rw [hz]
      exact C.defectNormal.pow_mem (C.defect_mem_defectNormal a) 2)
    X hX rho

/-- The residual form of the defect-square criterion: the square of one
pointwise compression defect, when it is a central involution, is invisible
in every operator-norm matrix approximation. -/
theorem defectSquare_centralInvolution_normMFInvisible
    [Countable E] (C : KazhdanCompressionCore Γ E) (a : Γ) (z : E)
    (hz : z = ⁅C.transported, C.iota a⁆ ^ 2)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g) :
    NormMFInvisible z :=
  C.centralInvolution_normMFInvisible z hz_sq hz_central
    (by
      rw [hz]
      exact C.defectNormal.pow_mem (C.defect_mem_defectNormal a) 2)

/-- **Central-sign criterion.**  A nontrivial central involution in the
Kazhdan-compression defect makes the ambient group non-MF. -/
theorem not_isOperatorMF_of_centralInvolution_mem_defect
    [Countable E] (C : KazhdanCompressionCore Γ E) (z : E)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (hz_ne : z ≠ 1) (hz_defect : z ∈ C.defectNormal) :
    ¬ IsOperatorMF E := by
  let F : Subgroup E := centralInvolutionSubgroup z hz_sq
  letI : Finite F := centralInvolutionSubgroup_finite z hz_sq
  letI : F.Normal := centralInvolutionSubgroup_normal z hz_sq hz_central
  letI : Nontrivial F :=
    centralInvolutionSubgroup_nontrivial z hz_sq hz_ne
  apply C.not_isOperatorMF_of_finiteNormal_le_defect F
  exact (centralInvolutionSubgroup_le_iff_mem z hz_sq C.defectNormal).mpr
    hz_defect

/-- **One-sign criterion.**  Let `d = t c t⁻¹` and
`u = [d, ι(a)]`.  If `z = u²` is a nontrivial central involution, then the
ambient group is not operator-MF.

This is the exact abstract statement behind the five-line proof in the
manuscript. -/
theorem not_isOperatorMF_of_defectSquare_eq_centralInvolution
    [Countable E] (C : KazhdanCompressionCore Γ E) (a : Γ) (z : E)
    (hz : z = ⁅C.transported, C.iota a⁆ ^ 2)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (hz_ne : z ≠ 1) :
    ¬ IsOperatorMF E := by
  apply C.not_isOperatorMF_of_centralInvolution_mem_defect
    z hz_sq hz_central hz_ne
  rw [hz]
  exact C.defectNormal.pow_mem (C.defect_mem_defectNormal a) 2

/-- **The central-sign criterion in the manuscript's exact coordinates.**
If the square of one compression defect is a nontrivial central involution,
then every homomorphism into every positive natural-dimensional genuine
norm-matrix C-star corona kills it, and the ambient countable group is not
MF in the literal CDE sense. -/
theorem manuscriptCentralSignCriterion :
    ManuscriptCentralSignCriterion := by
  intro Γ E _ _ _ hT iota t c hcompresses hcomm a z hz hz_ne hz_sq hz_central
  -- Step 0.  The printed countability hypothesis is exactly what puts the
  -- ambient group in `Type 0` up to isomorphism, so no hypothesis is added and
  -- no generality is lost.
  obtain ⟨E₀, _groupE₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model E
  haveI : Countable E₀ := Type0Transfer.countable_type0_model E e
  -- Step 1.  Carry the conjugation datum across the isomorphism.  Every field
  -- is a group-theoretic equation, so each is the image of the original.
  have hcompresses₀ : ∀ γ : Γ, ∃ δ : Γ,
      e t * (e.toMonoidHom.comp iota) γ * (e t)⁻¹ =
        (e.toMonoidHom.comp iota) δ := by
    intro γ
    obtain ⟨δ, hδ⟩ := hcompresses γ
    refine ⟨δ, ?_⟩
    have h : e (t * iota γ * t⁻¹) = e (iota δ) := by rw [hδ]
    simpa using h
  have hcomm₀ : ∀ γ : Γ, Commute (e c) ((e.toMonoidHom.comp iota) γ) := by
    intro γ
    simpa using (hcomm γ).map e
  let C₀ : KazhdanCompressionCore Γ E₀ := {
    iota := e.toMonoidHom.comp iota
    t := e t
    c := e c
    kazhdan := hasKazhdanPropertyT_iff_textbook.mpr hT
    compresses := hcompresses₀
    comm_c := hcomm₀
  }
  have hzC : e z = ⁅C₀.transported, C₀.iota a⁆ ^ 2 := by
    have h : e z = e (⁅t * c * t⁻¹, iota a⁆ ^ 2) := by rw [hz]
    simpa [C₀, KazhdanCompressionCore.transported, map_commutatorElement]
      using h
  have hz_sq₀ : (e z) ^ 2 = 1 := by rw [← map_pow, hz_sq, map_one]
  have hz_central₀ : ∀ g : E₀, Commute (e z) g := by
    intro g
    simpa using (hz_central (e.symm g)).map e
  have hz_ne₀ : e z ≠ 1 := fun h ↦
    hz_ne (e.injective (h.trans (map_one e).symm))
  -- Step 2.  Run the `Type 0` criterion on the model and pull both printed
  -- clauses back along the isomorphism.
  constructor
  · intro d hd
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    intro rho
    have h₀ := MonoidHom.mem_ker.mp
      (C₀.defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel
        a (e z) hzC hz_sq₀ hz_central₀
        (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd)
        (rho.comp e.symm.toMonoidHom))
    simpa using h₀
  · rw [isCDEOperatorMF_iff_isOperatorMF]
    intro hMF
    exact C₀.not_isOperatorMF_of_defectSquare_eq_centralInvolution
      a (e z) hzC hz_sq₀ hz_central₀ hz_ne₀
      (CommensurabilityInvariance.isOperatorMF_of_mulEquiv e hMF)

end KazhdanCompressionCore
end GroupApproximation
