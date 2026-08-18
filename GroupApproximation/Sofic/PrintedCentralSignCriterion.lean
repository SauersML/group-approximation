import GroupApproximation.Analysis.UltraproductRigidityRoute
import GroupApproximation.Sofic.KazhdanSignCriterion

/-!
# The central-sign criterion, on the printed transport

Proof-ledger row `KC.02`.  Its sentence, `p:constr-tietze`, is "rigidity forces
`u ∼₂ 1` while the Clifford model makes `u² = −1`", and the row cites the
headline `KazhdanCliffordConstruction.kazhdanCliffordConstruction`.

`Sofic/PrintedNegativeCornerKill.lean` put the *negative corner* of that
construction on the printed route, and the row records that this did not move
the headline: the headline's rigidity does not arrive through the corner at
all.  It arrives through `KazhdanCompressionCore.manuscriptCentralSignCriterion`,
and the transport step of that chain is the finite-stage one.

## The chain, and the single declaration it turns on

Both printed clauses of the criterion -- every genuine corona representation
kills `z`, and the ambient group is not CDE-operator-MF -- funnel through one
declaration:

  `manuscriptCentralSignCriterion`
    → `not_isOperatorMF_of_defectSquare_eq_centralInvolution`
      → `not_isOperatorMF_of_centralInvolution_mem_defect`
        → `not_isOperatorMF_of_finiteNormal_le_defect`
          → `finiteNormal_le_normMatrixCoronaKernel`
            → `finiteNormal_le_normMFResidual`

and, on the kernel side, `defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel`
→ `centralInvolution_mem_normMatrixCStarCoronaKernel`
→ `finiteNormal_le_normMatrixCStarCoronaKernel` → the same
`finiteNormal_le_normMFResidual`.  Everything between is bookkeeping: cutting
to the two-point subgroup `{1, z}`, transporting along the polar-correction
equivalence, and moving between the residual and kernel spellings.

`finiteNormal_le_normMFResidual` in turn is one application of
`finiteNormal_le_normMFResidual_of_hyperlinear_killed`, which *already* takes
the kill as a hypothesis -- that is the seam.  Its supplier is
`compressionDefects_eq_one_in_hyperlinearHom`, whose one transport step is
`compressionDefects_hsTrivial`, the finite-stage corner.

So exchanging the route costs exactly one substantive proof: the same
ultraproduct-hom kill, with `UltraproductRigidityRoute.compressionDefects_hsTrivial_literal`
-- hence `\ref{thm:kazhdan-transport}` by the printed §3 argument -- in place
of the finite-stage corner.  The rest of this file is that one exchange carried
up the chain, each declaration statement-identical to the one it shadows.

Nothing upstream is edited.  The finite-stage chain is left standing and still
proves the same statements; a consumer picks its route by picking a name, which
is the convention `Sofic/LiteralRouteTransport.lean` established for the
forward transport.
-/

namespace GroupApproximation
namespace PrintedCentralSign

open Filter KazhdanCornerMatrices KazhdanCompressorCorner KazhdanCompressionCore
open scoped commutatorElement Matrix.Norms.L2Operator

universe u w

variable {Γ E : Type} [Group Γ] [Group E]

/-! ## The one exchanged step -/

/-- **The compression defects die in the hyperlinear ultraproduct, by the
printed route.**  Statement-identical to
`KazhdanCompressionCore.compressionDefects_eq_one_in_hyperlinearHom`, with its
one transport step supplied by
`UltraproductRigidityRoute.compressionDefects_hsTrivial_literal` rather than by
the finite-stage corner.  Everything after the first line is the quotient
bookkeeping of the original, unchanged. -/
theorem compressionDefects_eq_one_in_hyperlinearHom_printed
    (C : KazhdanCompressionCore Γ E) (B : OpAlmostRepresentation E)
    {U : Ultrafilter ℕ} (hcof : (U : Filter ℕ) ≤ Filter.cofinite) :
    ∀ gamma : Γ,
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
          hcof ⁅C.transported, C.iota gamma⁆ = 1 := by
  intro gamma
  let S : AsymptoticUnitaryRepresentation E :=
    KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
  let rhoHS : E →* UniversalHyperlinear U S.model S.modelNonempty :=
    S.toUltraproductHom hcof
  have hcollapse :=
    UltraproductRigidityRoute.compressionDefects_hsTrivial_literal C B gamma
  have hnull :
      (fun n ↦ S.map n ⁅C.transported, C.iota gamma⁆)⁻¹ *
          (fun n ↦ S.map n 1) ∈
        nullUnitarySubgroup U S.model S.modelNonempty := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := hcollapse (epsilon / 2) (by linarith)
    refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
    show hsLengthSq (S.model n)
      (((S.map n ⁅C.transported, C.iota gamma⁆)⁻¹ * S.map n 1 :
        Matrix.unitaryGroup (S.model n) ℂ)) < epsilon
    rw [coe_inv_mul,
      hsLengthSq_conjTranspose_mul (S.model n)
        (S.map n ⁅C.transported, C.iota gamma⁆).2
        (S.modelNonempty n),
      KazhdanCompressorCorner.hsDistSq_comm]
    exact lt_of_le_of_lt (hN n hn) (by linarith)
  have heq :
      QuotientGroup.mk (fun n ↦ S.map n ⁅C.transported, C.iota gamma⁆) =
        QuotientGroup.mk (fun n ↦ S.map n 1) :=
    QuotientGroup.eq.mpr hnull
  change rhoHS ⁅C.transported, C.iota gamma⁆ = 1
  calc
    rhoHS ⁅C.transported, C.iota gamma⁆ =
        QuotientGroup.mk
          (fun n ↦ S.map n ⁅C.transported, C.iota gamma⁆) := rfl
    _ = QuotientGroup.mk (fun n ↦ S.map n 1) := heq
    _ = rhoHS 1 := rfl
    _ = 1 := map_one rhoHS

/-! ## The chain, re-formed on that step -/

/-- Finite normal subgroups of the compression defect lie in the norm-MF
residual, by the printed route. -/
theorem finiteNormal_le_normMFResidual_printed [Countable E]
    (C : KazhdanCompressionCore Γ E) (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal) :
    F ≤ normMFResidual E := by
  refine finiteNormal_le_normMFResidual_of_hyperlinear_killed
    C.defectNormal ?_ F hF
  intro B U hcof x hx
  exact MonoidHom.mem_ker.mp (C.defectNormal_le_ker
    ((toAsymptoticUnitaryRepresentation B).toUltraproductHom hcof)
    (compressionDefects_eq_one_in_hyperlinearHom_printed C B hcof) hx)

/-- The unitary-sequence kernel form, by the printed route. -/
theorem finiteNormal_le_normMatrixCoronaKernel_printed [Countable E]
    (C : KazhdanCompressionCore Γ E) (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : E →* NormMatrixCoronaUnitary X) :
    F ≤ rho.ker := by
  intro f hf
  have hinvisible : NormMFInvisible (f : E) :=
    mem_normMFResidual_iff.mp
      (finiteNormal_le_normMFResidual_printed C F hF hf)
  exact NormMFInvisible.toCoronaMFInvisible (G := E) hinvisible X hX rho

/-- The genuine C-star-corona kernel form, by the printed route. -/
theorem finiteNormal_le_normMatrixCStarCoronaKernel_printed [Countable E]
    (C : KazhdanCompressionCore Γ E) (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ rho.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  let sigma : E →* NormMatrixCoronaUnitary X :=
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho
  intro f hf
  have hkernel : f ∈ sigma.ker :=
    finiteNormal_le_normMatrixCoronaKernel_printed C F hF X hX sigma hf
  apply MonoidHom.mem_ker.mpr
  apply (normMatrixCoronaUnitaryEquiv X).symm.injective
  show (normMatrixCoronaUnitaryEquiv X).symm (rho f)
    = (normMatrixCoronaUnitaryEquiv X).symm 1
  have hsigma : sigma f = 1 := MonoidHom.mem_ker.mp hkernel
  rw [map_one]
  simpa [sigma] using hsigma

/-- A nontrivial finite normal subgroup inside the compression defect rules out
operator MF, by the printed route. -/
theorem not_isOperatorMF_of_finiteNormal_le_defect_printed [Countable E]
    (C : KazhdanCompressionCore Γ E) (F : Subgroup E) [Finite F] [F.Normal]
    [Nontrivial F] (hF : F ≤ C.defectNormal) :
    ¬ IsOperatorMF E := by
  rintro ⟨X, hX, rho, hrho⟩
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  have hker : (f : E) ∈ rho.ker :=
    finiteNormal_le_normMatrixCoronaKernel_printed C F hF X hX rho f.property
  have hfeq : (f : E) = 1 := by
    apply hrho
    simpa using (MonoidHom.mem_ker.mp hker)
  exact hf (Subtype.ext hfeq)

/-- A central involution in the defect is killed by every genuine corona
representation, by the printed route. -/
theorem centralInvolution_mem_normMatrixCStarCoronaKernel_printed [Countable E]
    (C : KazhdanCompressionCore Γ E) (z : E)
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
    (centralInvolutionSubgroup_le_iff_mem z hz_sq C.defectNormal).mpr hz_defect
  exact finiteNormal_le_normMatrixCStarCoronaKernel_printed C F hF X hX rho
    (involution_mem_centralInvolutionSubgroup z hz_sq)

/-- A nontrivial central involution in the defect rules out operator MF, by the
printed route. -/
theorem not_isOperatorMF_of_centralInvolution_mem_defect_printed [Countable E]
    (C : KazhdanCompressionCore Γ E) (z : E)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (hz_ne : z ≠ 1) (hz_defect : z ∈ C.defectNormal) :
    ¬ IsOperatorMF E := by
  let F : Subgroup E := centralInvolutionSubgroup z hz_sq
  letI : Finite F := centralInvolutionSubgroup_finite z hz_sq
  letI : F.Normal := centralInvolutionSubgroup_normal z hz_sq hz_central
  letI : Nontrivial F := centralInvolutionSubgroup_nontrivial z hz_sq hz_ne
  apply not_isOperatorMF_of_finiteNormal_le_defect_printed C F
  exact (centralInvolutionSubgroup_le_iff_mem z hz_sq C.defectNormal).mpr
    hz_defect

/-- The defect-square kernel form, by the printed route. -/
theorem defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel_printed
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
  exact centralInvolution_mem_normMatrixCStarCoronaKernel_printed C
    z hz_sq hz_central hz_defect X hX

/-- The one-sign criterion, by the printed route. -/
theorem not_isOperatorMF_of_defectSquare_eq_centralInvolution_printed
    [Countable E] (C : KazhdanCompressionCore Γ E) (a : Γ) (z : E)
    (hz : z = ⁅C.transported, C.iota a⁆ ^ 2)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (hz_ne : z ≠ 1) :
    ¬ IsOperatorMF E := by
  apply not_isOperatorMF_of_centralInvolution_mem_defect_printed C
    z hz_sq hz_central hz_ne
  rw [hz]
  exact C.defectNormal.pow_mem (C.defect_mem_defectNormal a) 2

/-! ## The criterion -/

/-- **`thm:sign-criterion`, on the printed transport.**

The same closed proposition `KazhdanCompressionCore.ManuscriptCentralSignCriterion`
that `manuscriptCentralSignCriterion` inhabits, proved through
`\ref{thm:kazhdan-transport}` instead of the finite-stage corner.  The proof is
that one, step for step -- the `Type 0` transfer of the datum is unchanged,
because the printed pinning is available at every compression core, so nothing
has to be carried across the isomorphism that was not carried before. -/
theorem manuscriptCentralSignCriterionPrinted :
    KazhdanCompressionCore.ManuscriptCentralSignCriterion := by
  intro Γ E _ _ _ hT iota t c hcompresses hcomm a z hz hz_ne hz_sq hz_central
  obtain ⟨E₀, _groupE₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model E
  haveI : Countable E₀ := Type0Transfer.countable_type0_model E e
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
  constructor
  · intro d hd
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    intro rho
    have h₀ := MonoidHom.mem_ker.mp
      (defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel_printed
        C₀ a (e z) hzC hz_sq₀ hz_central₀
        (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd)
        (rho.comp e.symm.toMonoidHom))
    simpa using h₀
  · rw [isCDEOperatorMF_iff_isOperatorMF]
    intro hMF
    exact not_isOperatorMF_of_defectSquare_eq_centralInvolution_printed
      C₀ a (e z) hzC hz_sq₀ hz_central₀ hz_ne₀
      (CommensurabilityInvariance.isOperatorMF_of_mulEquiv e hMF)

end PrintedCentralSign
end GroupApproximation
