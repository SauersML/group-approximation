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
premise-free blueprint must use nonnested, cyclic-overlap-controlled codewords;
it cannot obtain the required metric data from consecutive Nielsen pairs.
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

end

end LiteralAffineFreeProductAvatarChecks
end GroupApproximation
