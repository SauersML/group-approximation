import GroupApproximation.Computability.AdianRabinGeneral
import GroupApproximation.Computability.AdianRabinVariantTransform
import GroupApproximation.Computability.FixedLiteralMarkedQuery
import GroupApproximation.Sofic.NormMFResidualFunctorial

/-!
# Unconditional finite-presentation hardness of the fixed literal marked query

This file stays entirely inside the repository's concrete finite-presentation
syntax.  A fixed code for the literal non-MF group is inserted as the right
factor of the raw Adian--Rabin transformation.  The proved source-embedding
clause gives survival of the literal mark exactly when the input word is
nontrivial; the collapse clause gives an operator-MF target exactly when the
word is trivial, and MF-invisibility then forces every image of the mark to
die.

The result is an exact computable reduction from the complement of the coded
word problem to the executable fixed marked query.  It uses no Higman or
Chiodo compiler and makes no second-level finite-presentation claim.
-/

namespace GroupApproximation
namespace FixedLiteralMarkedQueryFiniteHardness

open PresentationCodes PresentationCodeList CoprodCode
open PresentedGroupRelabel RabinConstructionSource
open RabinVariantPresentation RabinVariantCode
open AdianRabinWordProblem FixedMarkedQueryHierarchy
open LiteralNonMFPresentation LiteralNonMFEndpoint
open FixedLiteralMarkedQuery

noncomputable section

/-- A fixed concrete presentation code for the literal group. -/
abbrev literalCode : PresentationCode :=
  (exists_code_mulEquiv MarkedGroup).choose

/-- The fixed code really presents the literal group. -/
def literalCodeEquiv : Carrier literalCode ≃* MarkedGroup :=
  (exists_code_mulEquiv MarkedGroup).choose_spec.some

/-- The raw, computable Adian--Rabin transform with the literal group as its
right free-product factor. -/
def transform (x : PresentationCode × List (ℕ × Bool)) : PresentationCode :=
  RawTransform.rawTransform x.1 literalCode x.2

theorem computable_transform : Computable transform :=
  RawTransformPrimrec.computable_rawTransform literalCode

private abbrev sourceCode (c : PresentationCode) : PresentationCode :=
  coprodCode c literalCode

private abbrev sourceRelators (c : PresentationCode) :
    Set (FreeGroup (Fin (genCount (sourceCode c)))) :=
  {x | x ∈ relatorListOf (sourceCode c)}

private abbrev sourceWord (c : PresentationCode) (w : List (ℕ × Bool)) :
    FreeGroup (Fin (genCount (sourceCode c))) :=
  wordOf (sourceCode c) (normWord c w)

/-- The literal group included in the right factor of the coded free product. -/
def literalToSourceCode (c : PresentationCode) :
    MarkedGroup →* Carrier (sourceCode c) :=
  (coprodCodeEquiv c literalCode).symm.toMonoidHom.comp
    ((inclRight {x | x ∈ relatorListOf c}
      {x | x ∈ relatorListOf literalCode}).comp
      ((carrierEquivList literalCode).toMonoidHom.comp
        literalCodeEquiv.symm.toMonoidHom))

theorem literalToSourceCode_injective (c : PresentationCode) :
    Function.Injective (literalToSourceCode c) :=
  (coprodCodeEquiv c literalCode).symm.injective.comp
    ((inclRight_injective
      {x | x ∈ relatorListOf c}
      {x | x ∈ relatorListOf literalCode}).comp
      ((carrierEquivList literalCode).injective.comp
        literalCodeEquiv.symm.injective))

/-- The explicit literal homomorphism through the surviving Rabin variant and
back across the raw-code equivalence. -/
def survivorHom (c : PresentationCode) (w : List (ℕ × Bool)) :
    MarkedGroup →* Carrier (transform (c, w)) :=
  (RawTransform.rawCarrierEquiv c literalCode w).symm.toMonoidHom.comp
    ((variantCodeEquiv (sourceCode c) (normWord c w)).symm.toMonoidHom.comp
      ((srcToPres (sourceRelators c) (sourceWord c w)).comp
        ((carrierEquivList (sourceCode c)).toMonoidHom.comp
          (literalToSourceCode c))))

/-- If the input word survives, the displayed homomorphism is injective. -/
theorem survivorHom_injective (c : PresentationCode) (w : List (ℕ × Bool))
    (hw : ¬ WordProblem c w) : Function.Injective (survivorHom c w) := by
  have hsource : PresentedGroup.mk (sourceRelators c) (sourceWord c w) ≠ 1 :=
    fun h ↦ hw ((AdianRabinGeneral.coprod_mk_eq_one_iff literalCode c w).1 h)
  exact (RawTransform.rawCarrierEquiv c literalCode w).symm.injective.comp
    ((variantCodeEquiv (sourceCode c) (normWord c w)).symm.injective.comp
      ((srcToPres_injective_of_ne_one (sourceRelators c) (sourceWord c w) hsource).comp
        ((carrierEquivList (sourceCode c)).injective.comp
          (literalToSourceCode_injective c))))

/-- Triviality of the input word makes the raw-transform target operator-MF. -/
theorem target_isOperatorMF_of_wordProblem (c : PresentationCode)
    (w : List (ℕ × Bool)) (hw : WordProblem c w) :
    IsOperatorMF (Carrier (transform (c, w))) := by
  have hsource : PresentedGroup.mk (sourceRelators c) (sourceWord c w) = 1 :=
    (AdianRabinGeneral.coprod_mk_eq_one_iff literalCode c w).2 hw
  have hvariant : IsOperatorMF
      (Carrier (variantCode (sourceCode c) (normWord c w))) :=
    variantCode_isOperatorMF (sourceCode c) (normWord c w) hsource
  exact hvariant.comap
    (RawTransform.rawCarrierEquiv c literalCode w).toMonoidHom
    (RawTransform.rawCarrierEquiv c literalCode w).injective

/-- Every homomorphism into an operator-MF target kills the fixed invisible
mark. -/
theorem map_mark_eq_one_of_isOperatorMF {G : Type*} [Group G] [Countable G]
    (hG : IsOperatorMF G) (f : MarkedGroup →* G) : f mark = 1 := by
  have hmem : f mark ∈ normMFResidual G :=
    mem_normMFResidual_iff.mpr (literal_mark_normMFInvisible.map f)
  rw [normMFResidual_eq_bot_of_isOperatorMF hG] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- The exact finite-presentation reduction: the executable literal query
survives precisely on nontrivial input words. -/
theorem survives_transform_iff_not_wordProblem
    (x : PresentationCode × List (ℕ × Bool)) :
    Survives literalQuery (transform x) ↔ ¬ wordProblemPred x := by
  obtain ⟨c, w⟩ := x
  constructor
  · intro hsurvive hword
    obtain ⟨f, hf⟩ := (survives_iff_homSurvives (transform (c, w))).1 hsurvive
    exact hf (map_mark_eq_one_of_isOperatorMF
      (target_isOperatorMF_of_wordProblem c w hword) f)
  · intro hword
    apply (survives_iff_homSurvives (transform (c, w))).2
    refine ⟨survivorHom c w, ?_⟩
    intro hmark
    apply LiteralNonMFLinearWitness.literal_mark_ne_one
    apply survivorHom_injective c w hword
    simpa using hmark

/-- Dually, the universal executable query holds precisely on trivial input
words. -/
theorem kills_transform_iff_wordProblem
    (x : PresentationCode × List (ℕ × Bool)) :
    Kills literalQuery (transform x) ↔ wordProblemPred x := by
  rw [kills_iff_not_survives, not_congr (survives_transform_iff_not_wordProblem x)]
  tauto

/-- The complement of the uniform finite-presentation word problem computably
many-one reduces to the fixed literal marked query. -/
theorem complementWordProblemReduction :
    (fun x ↦ ¬ wordProblemPred x) ≤₀ Survives literalQuery :=
  ⟨transform, computable_transform,
    fun x ↦ (survives_transform_iff_not_wordProblem x).symm⟩

/-- Survival of the fixed literal mark over finite-presentation codes is not
recursively enumerable. -/
theorem survives_not_re : ¬ REPred (Survives literalQuery) := by
  intro hre
  have hpull := MarkovMFConsequences.rePred_comp hre computable_transform
  exact WordProblemRE.not_rePred_compl_wordProblemPred
    (hpull.of_eq fun x ↦ survives_transform_iff_not_wordProblem x)

/-- The universal killing side is not co-r.e. -/
theorem kills_not_pi01 : ¬ ArithmeticalHierarchy.Pi01 (Kills literalQuery) := by
  intro h
  apply survives_not_re
  exact h.of_eq fun c ↦ by
    rw [kills_iff_not_survives]
    simp

end

end FixedLiteralMarkedQueryFiniteHardness
end GroupApproximation
