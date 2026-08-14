import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
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

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

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
theorem manuscriptCentralSignCriterion
    [Countable Γ] [Countable E]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* E) (t c : E)
    (hcompresses : ∀ γ : Γ, ∃ δ : Γ,
      t * iota γ * t⁻¹ = iota δ)
    (hcomm : ∀ γ : Γ, Commute c (iota γ))
    (a : Γ) (z : E)
    (hz : z = ⁅t * c * t⁻¹, iota a⁆ ^ 2)
    (hz_ne : z ≠ 1) (hz_sq : z ^ 2 = 1)
    (hz_central : ∀ g : E, Commute z g) :
    (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ rho : E →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho z = 1) ∧
      ¬ IsCDEOperatorMF E := by
  let C : KazhdanCompressionCore Γ E where
    iota := iota
    t := t
    c := c
    kazhdan := hasKazhdanPropertyT_iff_textbook.mpr hT
    compresses := hcompresses
    comm_c := hcomm
  have hzC : z = ⁅C.transported, C.iota a⁆ ^ 2 := by
    simpa [C, KazhdanCompressionCore.transported] using hz
  constructor
  · intro d hd
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    intro rho
    exact MonoidHom.mem_ker.mp
      (C.defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel
        a z hzC hz_sq hz_central
        (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd) rho)
  · rw [isCDEOperatorMF_iff_isOperatorMF]
    exact C.not_isOperatorMF_of_defectSquare_eq_centralInvolution
      a z hzC hz_sq hz_central hz_ne

end KazhdanCompressionCore
end GroupApproximation
