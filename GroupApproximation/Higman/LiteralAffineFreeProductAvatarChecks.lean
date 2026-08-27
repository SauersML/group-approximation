import GroupApproximation.Higman.LiteralAffineFreeProductPaddedAvatarBlueprint
import GroupApproximation.Sofic.GreendlingerPiece
import GroupApproximation.Meta.AxiomGuard

/-!
# Metric audit of the marked Nielsen-padded affine avatar

The marked positive padding is a correct Tietze transformation, but its two
relators over each old relator are nested.  After positive avatar substitution
the whole shorter word remains a prefix of the longer word.  Since both belong
to the symmetrized router family and have different lengths, the shorter word
is a piece.  No `C'(lambda)` condition with `lambda < 1` can hold.

This file permanently fences that failed route at the exact public handoff:
`ConcreteRemainingRouterChecks d` is empty for every padding depth.  A future
premise-free blueprint cannot merely replace the Nielsen padding by nonnested
private codewords.  The second audit below proves the deeper obstruction: any
positive doubled presentation still has the two-letter kernel word `x xbar`.
If the router relator floor is at least twice the norm of that word's avatar,
the sharp Greendlinger gate contradicts well-definedness of the source map.
-/

namespace GroupApproximation
namespace LiteralAffineFreeProductAvatarChecks

open SmallCancellationRouter
open BespokeRouter.AvatarWordFamily
open LiteralAffineFreeProductAvatarBlueprint
open LiteralAffineFreeProductPaddedAvatarBlueprint
open LiteralAffineFreeProductPaddedAvatarBlueprint.PositiveMarkedPadding

noncomputable section

/-- Avatar substitution preserves concatenation. -/
theorem avatarSubst_append {A : Type} (W : A → List (Fin 2 × Bool))
    (u v : List (A × Bool)) :
    avatarSubst W (u ++ v) = avatarSubst W u ++ avatarSubst W v := by
  simp [avatarSubst, List.map_append, List.flatten_append]

/-- The shorter expanded source relator attached to the chosen anchor. -/
def shortRelator (d : ℕ) : List (Fin 2 × Bool) :=
  avatarSubst (blueprint d).srcAvatarWord
    (codedRelator sourcePositiveWordPresentation d sourceAnchor)

/-- Its consecutive, longer Nielsen mate. -/
def longRelator (d : ℕ) : List (Fin 2 × Bool) :=
  avatarSubst (blueprint d).srcAvatarWord
    (codedRelator sourcePositiveWordPresentation (d + 1) sourceAnchor)

theorem shortRelator_mem (d : ℕ) :
    shortRelator d ∈ (blueprint d).relators := by
  apply (blueprint d).mem_relators_src
  change codedRelator sourcePositiveWordPresentation d sourceAnchor ∈
    rel sourcePositiveWordPresentation d
  exact Set.mem_union_left _ ⟨sourceAnchor, sourceAnchor_mem, rfl⟩

theorem longRelator_mem (d : ℕ) :
    longRelator d ∈ (blueprint d).relators := by
  apply (blueprint d).mem_relators_src
  change codedRelator sourcePositiveWordPresentation (d + 1) sourceAnchor ∈
    rel sourcePositiveWordPresentation d
  exact Set.mem_union_right _ ⟨sourceAnchor, sourceAnchor_mem, rfl⟩

/-- Positivity means the nesting survives avatar substitution literally. -/
theorem shortRelator_prefix_longRelator (d : ℕ) :
    shortRelator d <+: longRelator d := by
  unfold shortRelator longRelator
  unfold LiteralAffineFreeProductPaddedAvatarBlueprint.blueprint
    LiteralAffineFreeProductPaddedAvatarBlueprint.sourceData
    sourcePaddedPresentation presentation Blueprint.srcAvatarWord
    Blueprint.srcPres
  rw [codedRelator_succ]
  exact ⟨avatarSubst _ (padList sourceAnchor),
    (avatarSubst_append _ _ _).symm⟩

/-- The two expanded relators have different lengths. -/
theorem shortRelator_ne_longRelator (d : ℕ) :
    shortRelator d ≠ longRelator d := by
  intro h
  have hlen := congrArg List.length h
  have hs : (shortRelator d).length =
      (1 + d * sourceAnchor.length) * (blueprint d).avatarLength := by
    unfold shortRelator
    rw [length_avatarSubst_eq (blueprint d).srcAvatarWord
      (blueprint d).avatarLength (blueprint d).length_srcAvatarWord]
    have hu := length_codedRelator sourcePositiveWordPresentation d sourceAnchor
    exact congrArg (fun n ↦ n * (blueprint d).avatarLength) hu
  have hl : (longRelator d).length =
      (1 + (d + 1) * sourceAnchor.length) * (blueprint d).avatarLength := by
    unfold longRelator
    rw [length_avatarSubst_eq (blueprint d).srcAvatarWord
      (blueprint d).avatarLength (blueprint d).length_srcAvatarWord]
    have hv := length_codedRelator sourcePositiveWordPresentation
      (d + 1) sourceAnchor
    exact congrArg (fun n ↦ n * (blueprint d).avatarLength) hv
  rw [hs, hl] at hlen
  have ha : 0 < sourceAnchor.length := List.length_pos_iff.mpr sourceAnchor_ne_nil
  have hS : 0 < (blueprint d).avatarLength :=
    lt_of_lt_of_le (by decide) (blueprint d).sixteen_le_avatarLength
  nlinarith

/-- The whole shorter relator is a piece. -/
theorem shortRelator_isPiece (d : ℕ) :
    IsPiece (symmetrization (blueprint d).relators) (shortRelator d) := by
  exact isPiece_of_prefix_two
    (subset_symmetrization _ (shortRelator_mem d))
    (subset_symmetrization _ (longRelator_mem d))
    (shortRelator_ne_longRelator d)
    (List.prefix_refl _)
    (shortRelator_prefix_longRelator d)

/-- Any metric constant strictly below one is contradicted by the full-relator
piece. -/
theorem not_metricSmallCancellation_of_lt_one (d : ℕ) {lam : ℚ}
    (hlam : lam < 1) :
    ¬ MetricSmallCancellation (blueprint d).relators lam := by
  intro hmetric
  have h := hmetric (shortRelator d) (shortRelator_isPiece d)
    (shortRelator d) (subset_symmetrization _ (shortRelator_mem d))
    (List.prefix_refl _)
  have hpos : 0 < (shortRelator d).length := by
    have hs : (shortRelator d).length =
        (1 + d * sourceAnchor.length) * (blueprint d).avatarLength := by
      unfold shortRelator
      rw [length_avatarSubst_eq (blueprint d).srcAvatarWord
        (blueprint d).avatarLength (blueprint d).length_srcAvatarWord]
      have hu := length_codedRelator sourcePositiveWordPresentation d sourceAnchor
      exact congrArg (fun n ↦ n * (blueprint d).avatarLength) hu
    rw [hs]
    have hS : 0 < (blueprint d).avatarLength :=
      lt_of_lt_of_le (by decide) (blueprint d).sixteen_le_avatarLength
    positivity
  have hqpos : (0 : ℚ) < (shortRelator d).length := by exact_mod_cast hpos
  nlinarith

/-- In particular the exact residual checklist exposed by the padding module
has no inhabitant. -/
theorem not_concreteRemainingRouterChecks (d : ℕ) :
    IsEmpty (ConcreteRemainingRouterChecks d) := by
  constructor
  intro H
  let I := inputsOfRemaining d H
  exact not_metricSmallCancellation_of_lt_one d (by norm_num : (1 : ℚ) / 8 < 1)
    I.metricData.metric_eighth

/-- The closed proposition audited below. -/
def AllDepthsNoGo : Prop :=
  ∀ d : ℕ, IsEmpty (ConcreteRemainingRouterChecks d)

/-- Closed universal audit: no padding depth repairs the nested Nielsen pair. -/
theorem all_depths_no_go : AllDepthsNoGo :=
  not_concreteRemainingRouterChecks

#audit_closed_axioms all_depths_no_go

/-! ## The structural doubled-presentation obstruction

The preceding proof only sees the accidental nesting of consecutive Nielsen
relators.  The theorem below does not inspect the relator spelling at all.  It
uses the exact router interface: a source-kernel word dies in the routed
quotient, while the sharp Greendlinger gate says that a nontrivial word in the
relator subgroup is longer than half of some symmetrized relator.  Thus no
router input can put the common relator floor above twice that word's norm.
-/

/-- General floor obstruction at the exact `AvatarRouterInstance.Inputs`
handoff.  This theorem is independent of how the positive source relators were
padded or marked. -/
theorem no_go_of_short_source_kernel
    {E : Type} [Group E] {N : Subgroup E} {s : E}
    {B : Type} [Group B]
    {D : Blueprint E N s B} (I : AvatarRouterInstance.Inputs D)
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1)
    (hres : SharpResiduals (Fin 2))
    (x : FreeGroup (Fin D.srcPres.card))
    (hxker : D.srcPres.hom x = 1)
    (hxne : FreeGroup.lift D.srcAvatar x ≠ 1)
    (hshort : 2 * FreeGroup.norm (FreeGroup.lift D.srcAvatar x) ≤
      I.relatorFloor) : False := by
  let R := I.design hne
  have hxker' : x ∈ R.srcHom.ker := by
    exact MonoidHom.mem_ker.mpr hxker
  have hxquot : R.srcAvatar x = 1 :=
    MonoidHom.mem_ker.mp (R.srcHom_ker_le_avatar_ker hxker')
  have hxmem : FreeGroup.lift D.srcAvatar x ∈
      Subgroup.normalClosure (FreeGroup.mk '' D.relators) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact hxquot
  obtain ⟨r, hr, hlt⟩ := GreendlingerFreeGate.norm_bound_of_sharpGate
    (sharpGate_fin_two_of_residuals hres)
    R.relators_cyclicallyReduced R.metric hxne hxmem
  have hfloor : I.relatorFloor ≤ r.length := I.metricData.floor_le_length hr
  omega

/-- The closed, universe-polymorphic statement audited below. -/
def ShortSourceKernelFloorNoGo : Prop :=
  ∀ (E : Type) [Group E] (N : Subgroup E) (s : E)
    (B : Type) [Group B] (D : Blueprint E N s B)
    (I : AvatarRouterInstance.Inputs D)
    (_hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1)
    (_hres : SharpResiduals (Fin 2))
    (x : FreeGroup (Fin D.srcPres.card)),
    D.srcPres.hom x = 1 →
    FreeGroup.lift D.srcAvatar x ≠ 1 →
    2 * FreeGroup.norm (FreeGroup.lift D.srcAvatar x) ≤ I.relatorFloor →
    False

/-- Closed audit of the general interface-level obstruction. -/
theorem short_source_kernel_floor_no_go : ShortSourceKernelFloorNoGo := by
  intro E _ N s B _ D I hne hres x hxker hxne hshort
  exact no_go_of_short_source_kernel I hne hres x hxker hxne hshort

#audit_closed_axioms short_source_kernel_floor_no_go

/-! ### The unavoidable length-two word in the concrete doubled source -/

/-- The original source presentation has a generator because its target has a
certified nontrivial element. -/
def sourcePairIndex : Fin sourceWordPresentation.card :=
  ⟨0, card_pos_of_ne_one sourceWordPresentation
    LiteralAffineFreeProductBassSerre.crossingDefect_ne_one⟩

/-- The positive doubled presentation's unavoidable relation `x xbar`. -/
def sourcePairWord :
    List (Fin blueprint.srcPres.card × Bool) :=
  PositivePresentation.pairWord sourceWordPresentation sourcePairIndex

/-- The doubled pair word is killed by the concrete source presentation map,
even though finite extraction need not choose it as a defining relator. -/
theorem sourcePairWord_mem_ker :
    blueprint.srcPres.hom (FreeGroup.mk sourcePairWord) = 1 := by
  exact (PositivePresentation.pairWord_mem sourceWordPresentation sourcePairIndex).2

/-- Its avatar has exactly two balanced avatar blocks and no cancellation. -/
theorem sourcePairAvatar_norm :
    FreeGroup.norm
        (FreeGroup.lift blueprint.srcAvatar (FreeGroup.mk sourcePairWord)) =
      2 * blueprint.avatarLength := by
  let out := avatarSubst blueprint.srcAvatarWord sourcePairWord
  have hwpos : ∀ c ∈ sourcePairWord, c.2 = true :=
    (PositivePresentation.pairWord_mem sourceWordPresentation sourcePairIndex).1
  have hapos : ∀ k, ∀ c ∈ blueprint.srcAvatarWord k, c.2 = true :=
    fun k ↦ forall_positive_avatarWord blueprint.avatarCount blueprint.codeL (k : ℕ)
  have houtpos : ∀ c ∈ out, c.2 = true :=
    forall_positive_avatarSubst blueprint.srcAvatarWord hapos hwpos
  have hwlen : sourcePairWord.length = 2 := by
    rfl
  have houtlen : out.length = 2 * blueprint.avatarLength := by
    calc
      out.length = sourcePairWord.length * blueprint.avatarLength :=
        length_avatarSubst_eq blueprint.srcAvatarWord blueprint.avatarLength
          blueprint.length_srcAvatarWord sourcePairWord
      _ = 2 * blueprint.avatarLength := congrArg
        (fun n ↦ n * blueprint.avatarLength) hwlen
  rw [lift_mk_eq_mk_avatarSubst blueprint.srcAvatarWord blueprint.srcAvatar
    (fun _ ↦ rfl) sourcePairWord]
  change (FreeGroup.mk out).toWord.length = 2 * blueprint.avatarLength
  rw [AvatarMetricCheck.toWord_mk_of_forall_positive houtpos, houtlen]

/-- The doubled pair's avatar is nontrivial. -/
theorem sourcePairAvatar_ne_one :
    FreeGroup.lift blueprint.srcAvatar (FreeGroup.mk sourcePairWord) ≠ 1 := by
  intro h
  have hn := sourcePairAvatar_norm
  rw [h, FreeGroup.norm_one] at hn
  have hS : 0 < blueprint.avatarLength :=
    lt_of_lt_of_le (by decide) blueprint.sixteen_le_avatarLength
  omega

/-- No exact input using the balanced avatar length and a floor of four avatar
blocks can pass the sharp router residuals.  This is the promised no-go for
every redesign that keeps the same positive doubled-presentation/avatar
interface, regardless of its private codewords or occurrence marks. -/
theorem no_doubled_blueprint_inputs
    (I : AvatarRouterInstance.Inputs blueprint)
    (havatar : I.avatarLen = blueprint.avatarLength)
    (hfloor : 4 ≤ I.wordFloor)
    (hres : SharpResiduals (Fin 2)) : False := by
  apply no_go_of_short_source_kernel I blueprint_protectedWord_ne_one hres
    (FreeGroup.mk sourcePairWord) sourcePairWord_mem_ker sourcePairAvatar_ne_one
  change 2 * FreeGroup.norm
      (FreeGroup.lift blueprint.srcAvatar (FreeGroup.mk sourcePairWord)) ≤
    I.wordFloor * I.avatarLen
  rw [sourcePairAvatar_norm, havatar]
  nlinarith

/-- Closed formulation of the exact concrete doubled-interface obstruction. -/
def DoubledBlueprintInputsNoGo : Prop :=
  ∀ (I : AvatarRouterInstance.Inputs blueprint),
    I.avatarLen = blueprint.avatarLength →
    4 ≤ I.wordFloor →
    SharpResiduals (Fin 2) → False

/-- Closed audit: private-generator redesigns cannot evade the doubled pair. -/
theorem doubled_blueprint_inputs_no_go : DoubledBlueprintInputsNoGo :=
  no_doubled_blueprint_inputs

#audit_closed_axioms doubled_blueprint_inputs_no_go

end

end LiteralAffineFreeProductAvatarChecks
end GroupApproximation
