import GroupApproximation.KunThom.RelativeFunctorAssembly
import Mathlib.Data.Real.Archimedean

/-!
# Improving transported representatives for the relative cluster functor

`GroupoidPresentation.ClusterMetric.relativeFunctor` (Kun--Thom, arXiv:2608.06222v3,
Lemma 4.3) takes, besides the bridge bound, the hypothesis `himprove`, that every
transported representative lies within `ρ` of a target representative, and the three
numerical families `hrespects`, `hcomp` and `hfaithful`.  This file supplies all four when
source and target are the cluster groupoids of `ScaledPartialClusterSystem`s.

* `himprove_of_defects`: a transported representative whose forward and backward
  equivariance defects are below `K₀ h min (scale X) (scale Y) / 2` is repaired by
  `ScaledPartialClusterSystem.repair_spec` into a target representative within
  `d |model X|` of it.
* `improveRadius`: `⌊d |model (obj X)|⌋₊ + 1`.  It exceeds the distance bound of the
  repair (`lt_improveRadius`), and it is at most a hundredth of the target scale once
  `0 ≤ d ≤ 1 / 3800` and the scale is at least `200` (`hundred_mul_improveRadius_le`).
* `scale_comparable_of_rep` and `scale_comparable_of_bridge`: a representative, and a
  bridge whose unmatched mass is at most a hundredth of the target scale, keep the scales
  at its two ends within `11 / 10`.
* `respects_of_small`, `comp_of_small` and `faithful_of_small`: the numerical hypotheses
  of `relativeFunctor` in their exact shapes, from bridge masses and radii at most a
  hundredth of the target scale.
* `scaledRelativeFunctor` and `scaledRelativeFunctor_faithful`: the relative functor
  between scaled cluster groupoids, assembled from these.

The radius `ρ` comes from the distance bound `d |model X|` of the repair, which is small
against the scales, rather than from the target radius `2 min (scale X) (scale Y)`.  With
it each numerical family holds with a wide margin.
-/

namespace GroupApproximation
namespace RelativeFunctorImprove

open CategoryTheory FinitePartialBijection

universe u u' v

/-! ### Improvement from small defects -/

/-- **Improvement of transported representatives.**  If the transport of every source
representative through the bridges has forward and backward equivariance defects below
`K₀ h min (scale X) (scale Y) / 2` in a scaled cluster system, then its repair is a target
representative within `d |model X|` of it, hence within any radius above that bound. -/
theorem himprove_of_defects {I : Type u} {J : Type u'} [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    {P : GroupoidPresentation.{u, v} I} (MP : P.ClusterMetric)
    (DQ : ScaledPartialClusterSystem J L) {R : Set I} {D : Set J} (obj : R → D)
    (bridge : ∀ X : R,
      FinitePartialBijection (MP.model X.1) (DQ.clusterMetric.model (obj X).1))
    (ρ : R → R → ℕ)
    (hforward : ∀ (X Y : R) (b : P.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) (MP.val b)).equivarianceDefect
          (DQ.act (obj X).1) (DQ.act (obj Y).1)).card : ℝ) <
        DQ.K₀ * DQ.h * ((min (DQ.scale (obj X).1) (DQ.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hbackward : ∀ (X Y : R) (b : P.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) (MP.val b)).symm.equivarianceDefect
          (DQ.act (obj Y).1) (DQ.act (obj X).1)).card : ℝ) <
        DQ.K₀ * DQ.h * ((min (DQ.scale (obj X).1) (DQ.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hρ : ∀ X Y : R, DQ.d * Fintype.card (DQ.model (obj X).1) < ρ X Y) :
    ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : DQ.presentation.Rep (obj X).1 (obj Y).1,
      (DQ.clusterMetric.val r).twoSidedDisagreement
        (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y := by
  intro X Y b
  obtain ⟨hcand, -, hdist⟩ := DQ.repair_spec (X := (obj X).1) (Y := (obj Y).1)
    (sandwich (bridge X) (bridge Y) (MP.val b)) (hforward X Y b) (hbackward X Y b)
  have hmem : DQ.repair (X := (obj X).1) (Y := (obj Y).1)
      (sandwich (bridge X) (bridge Y) (MP.val b)) ∈
        DQ.clusterData.candidate (obj X).1 (obj Y).1 :=
    (FinitePartialBijection.mem_clusterCandidates (DQ.act (obj X).1) (DQ.act (obj Y).1) DQ.h
      (min (DQ.scale (obj X).1) (DQ.scale (obj Y).1)) _).mpr hcand
  refine ⟨(⟨_, hmem⟩ : DQ.clusterData.Rep (obj X).1 (obj Y).1), ?_⟩
  have hlt : (((DQ.repair (X := (obj X).1) (Y := (obj Y).1)
      (sandwich (bridge X) (bridge Y) (MP.val b))).twoSidedDisagreement
        (sandwich (bridge X) (bridge Y) (MP.val b)) : ℕ) : ℝ) < ρ X Y :=
    hdist.trans_lt (hρ X Y)
  show (DQ.repair (X := (obj X).1) (Y := (obj Y).1)
      (sandwich (bridge X) (bridge Y) (MP.val b))).twoSidedDisagreement
        (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y
  exact_mod_cast hlt

/-! ### The improvement radius -/

/-- The improvement radius at a pair of retained objects: one more than the integer part
of the distance bound `d |model (obj X)|` of the target system. -/
noncomputable def improveRadius {I : Type u} {J : Type u'} [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DQ : ScaledPartialClusterSystem J L) {R : Set I} {D : Set J} (obj : R → D)
    (X _Y : R) : ℕ :=
  ⌊DQ.d * Fintype.card (DQ.model (obj X).1)⌋₊ + 1

/-- The improvement radius exceeds the distance bound of the repair. -/
theorem lt_improveRadius {I : Type u} {J : Type u'} [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DQ : ScaledPartialClusterSystem J L) {R : Set I} {D : Set J} (obj : R → D)
    (X Y : R) :
    DQ.d * Fintype.card (DQ.model (obj X).1) < improveRadius DQ obj X Y := by
  have h := Nat.lt_floor_add_one (DQ.d * (Fintype.card (DQ.model (obj X).1) : ℝ))
  unfold improveRadius
  exact_mod_cast h

/-- Once the distance factor is at most `1 / 3800` and the target scale is at least `200`,
the improvement radius is at most a hundredth of the target scale. -/
theorem hundred_mul_improveRadius_le {I : Type u} {J : Type u'} [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DQ : ScaledPartialClusterSystem J L) {R : Set I} {D : Set J} (obj : R → D)
    (hd0 : 0 ≤ DQ.d) (hd : DQ.d ≤ 1 / 3800) (X Y : R)
    (hscale : 200 ≤ DQ.scale (obj X).1) :
    100 * improveRadius DQ obj X Y ≤ DQ.scale (obj X).1 := by
  have heq := DQ.scale_eq (obj X).1
  have hcardNat : Fintype.card (DQ.model (obj X).1) ≤ 19 * DQ.scale (obj X).1 := by omega
  have hcard : (Fintype.card (DQ.model (obj X).1) : ℝ) ≤ 19 * (DQ.scale (obj X).1 : ℝ) := by
    exact_mod_cast hcardNat
  have h1 : DQ.d * Fintype.card (DQ.model (obj X).1) ≤
      DQ.d * (19 * (DQ.scale (obj X).1 : ℝ)) :=
    mul_le_mul_of_nonneg_left hcard hd0
  have h2 : DQ.d * (19 * (DQ.scale (obj X).1 : ℝ)) ≤
      1 / 3800 * (19 * (DQ.scale (obj X).1 : ℝ)) :=
    mul_le_mul_of_nonneg_right hd (by positivity)
  have hfloor : (⌊DQ.d * Fintype.card (DQ.model (obj X).1)⌋₊ : ℝ) ≤
      DQ.d * Fintype.card (DQ.model (obj X).1) :=
    Nat.floor_le (mul_nonneg hd0 (Nat.cast_nonneg _))
  have hsR : (200 : ℝ) ≤ DQ.scale (obj X).1 := by exact_mod_cast hscale
  have hreal : (100 : ℝ) * ((⌊DQ.d * Fintype.card (DQ.model (obj X).1)⌋₊ : ℝ) + 1) ≤
      DQ.scale (obj X).1 := by
    linarith
  unfold improveRadius
  exact_mod_cast hreal

/-! ### Comparable scales -/

/-- A representative of a scaled cluster groupoid keeps the scales of its two objects
within `11 / 10`. -/
theorem scale_comparable_of_rep {I : Type u} [Fintype I]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DP : ScaledPartialClusterSystem I L) {X Y : I} (b : DP.clusterData.Rep X Y) :
    10 * DP.scale X ≤ 11 * DP.scale Y ∧ 10 * DP.scale Y ≤ 11 * DP.scale X := by
  have hb := (FinitePartialBijection.mem_clusterCandidates (DP.act X) (DP.act Y) DP.h
    (min (DP.scale X) (DP.scale Y)) b.1).mp b.2
  have hsymm := hb.symm
  rw [min_comm] at hsymm
  exact ⟨DP.scale_comparable hb, DP.scale_comparable hsymm⟩

/-- A bridge whose unmatched mass is at most a hundredth of the target scale keeps the
source and target scales within `11 / 10`. -/
theorem scale_comparable_of_bridge {I : Type u} {J : Type u'} [Fintype I] [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DP : ScaledPartialClusterSystem I L) (DQ : ScaledPartialClusterSystem J L)
    {X : I} {X' : J} (w : FinitePartialBijection (DP.model X) (DQ.model X')) {β : ℕ}
    (hw : w.sourceDefect + w.targetDefect ≤ β) (hβ : 100 * β ≤ DQ.scale X') :
    10 * DP.scale X ≤ 11 * DQ.scale X' ∧ 10 * DQ.scale X' ≤ 11 * DP.scale X := by
  have h1 := CentralizerNormalizationImprove.card_source_le_card_target_add w
  have h2 := CentralizerNormalizationImprove.card_target_le_card_source_add w
  have hX := DP.scale_eq X
  have hX' := DQ.scale_eq X'
  have hl := DP.scale_large X
  have hl' := DQ.scale_large X'
  constructor <;> omega

/-! ### The numerical hypotheses of the relative functor -/

/-- **`hrespects`** for scaled cluster groupoids, from bridge masses and radii at most a
hundredth of the target scale. -/
theorem respects_of_small {I : Type u} {J : Type u'} [Fintype I] [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DP : ScaledPartialClusterSystem I L) (DQ : ScaledPartialClusterSystem J L)
    {R : Set I} {D : Set J} (obj : R → D)
    (bridge : ∀ X : R,
      FinitePartialBijection (DP.clusterMetric.model X.1) (DQ.clusterMetric.model (obj X).1))
    (β : R → ℕ) (ρ : R → R → ℕ)
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (hβ : ∀ X : R, 100 * β X ≤ DQ.scale (obj X).1)
    (hρ : ∀ X Y : R, 100 * ρ X Y ≤ DQ.scale (obj X).1) :
    ∀ {X Y : R}, DP.presentation.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + DP.clusterMetric.radius X.1 Y.1 ≤
        8 * DQ.clusterMetric.radius (obj X).1 (obj Y).1 := by
  intro X Y b
  obtain ⟨hXY, hYX⟩ := scale_comparable_of_rep DP (X := X.1) (Y := Y.1) b
  obtain ⟨hXt, htX⟩ := scale_comparable_of_bridge DP DQ (X := X.1) (X' := (obj X).1)
    (bridge X) (hbridge X) (hβ X)
  obtain ⟨hYt, htY⟩ := scale_comparable_of_bridge DP DQ (X := Y.1) (X' := (obj Y).1)
    (bridge Y) (hbridge Y) (hβ Y)
  have hβX := hβ X
  have hβY := hβ Y
  have hρXY := hρ X Y
  have hm1 := min_le_left (DP.scale X.1) (DP.scale Y.1)
  have hm2 := min_le_right (DP.scale X.1) (DP.scale Y.1)
  have hn1 := min_le_left (DQ.scale (obj X).1) (DQ.scale (obj Y).1)
  have hn2 := min_le_right (DQ.scale (obj X).1) (DQ.scale (obj Y).1)
  show 2 * ρ X Y + β X + β Y + 2 * min (DP.scale X.1) (DP.scale Y.1) ≤
    8 * (2 * min (DQ.scale (obj X).1) (DQ.scale (obj Y).1))
  rcases min_choice (DQ.scale (obj X).1) (DQ.scale (obj Y).1) with hn | hn
  · linarith
  · linarith

/-- **`hcomp`** for scaled cluster groupoids, from bridge masses and radii at most a
hundredth of the target scale. -/
theorem comp_of_small {I : Type u} {J : Type u'} [Fintype I] [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DP : ScaledPartialClusterSystem I L) (DQ : ScaledPartialClusterSystem J L)
    {R : Set I} {D : Set J} (obj : R → D)
    (bridge : ∀ X : R,
      FinitePartialBijection (DP.clusterMetric.model X.1) (DQ.clusterMetric.model (obj X).1))
    (β : R → ℕ) (ρ : R → R → ℕ)
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (hβ : ∀ X : R, 100 * β X ≤ DQ.scale (obj X).1)
    (hρ : ∀ X Y : R, 100 * ρ X Y ≤ DQ.scale (obj X).1) :
    ∀ {X Y Z : R}, DP.presentation.Rep X.1 Y.1 → DP.presentation.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + DP.clusterMetric.radius X.1 Z.1 +
        DP.clusterMetric.radius X.1 Y.1 + DP.clusterMetric.radius Y.1 Z.1 +
          DQ.clusterMetric.radius (obj X).1 (obj Z).1 ≤
            8 * DQ.clusterMetric.radius (obj X).1 (obj Z).1 := by
  intro X Y Z f g
  obtain ⟨hXY, hYX⟩ := scale_comparable_of_rep DP (X := X.1) (Y := Y.1) f
  obtain ⟨hYZ, hZY⟩ := scale_comparable_of_rep DP (X := Y.1) (Y := Z.1) g
  obtain ⟨hXt, htX⟩ := scale_comparable_of_bridge DP DQ (X := X.1) (X' := (obj X).1)
    (bridge X) (hbridge X) (hβ X)
  obtain ⟨hYt, htY⟩ := scale_comparable_of_bridge DP DQ (X := Y.1) (X' := (obj Y).1)
    (bridge Y) (hbridge Y) (hβ Y)
  obtain ⟨hZt, htZ⟩ := scale_comparable_of_bridge DP DQ (X := Z.1) (X' := (obj Z).1)
    (bridge Z) (hbridge Z) (hβ Z)
  have hβX := hβ X
  have hβY := hβ Y
  have hβZ := hβ Z
  have hρXZ := hρ X Z
  have hρXY := hρ X Y
  have hρYZ := hρ Y Z
  have hXZ1 := min_le_left (DP.scale X.1) (DP.scale Z.1)
  have hXZ2 := min_le_right (DP.scale X.1) (DP.scale Z.1)
  have hXY1 := min_le_left (DP.scale X.1) (DP.scale Y.1)
  have hXY2 := min_le_right (DP.scale X.1) (DP.scale Y.1)
  have hYZ1 := min_le_left (DP.scale Y.1) (DP.scale Z.1)
  have hYZ2 := min_le_right (DP.scale Y.1) (DP.scale Z.1)
  show ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z +
      2 * min (DP.scale X.1) (DP.scale Z.1) + 2 * min (DP.scale X.1) (DP.scale Y.1) +
        2 * min (DP.scale Y.1) (DP.scale Z.1) +
          2 * min (DQ.scale (obj X).1) (DQ.scale (obj Z).1) ≤
            8 * (2 * min (DQ.scale (obj X).1) (DQ.scale (obj Z).1))
  rcases min_choice (DQ.scale (obj X).1) (DQ.scale (obj Z).1) with hn | hn
  · linarith
  · linarith

/-- **`hfaithful`** for scaled cluster groupoids, from bridge masses and radii at most a
hundredth of the target scale. -/
theorem faithful_of_small {I : Type u} {J : Type u'} [Fintype I] [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DP : ScaledPartialClusterSystem I L) (DQ : ScaledPartialClusterSystem J L)
    {R : Set I} {D : Set J} (obj : R → D)
    (bridge : ∀ X : R,
      FinitePartialBijection (DP.clusterMetric.model X.1) (DQ.clusterMetric.model (obj X).1))
    (β : R → ℕ) (ρ : R → R → ℕ)
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (hβ : ∀ X : R, 100 * β X ≤ DQ.scale (obj X).1)
    (hρ : ∀ X Y : R, 100 * ρ X Y ≤ DQ.scale (obj X).1) :
    ∀ {X Y : R}, DP.presentation.Rep X.1 Y.1 →
      2 * ρ X Y + 5 * β X + 5 * β Y + 2 * DP.clusterMetric.radius X.1 Y.1 +
          DQ.clusterMetric.radius (obj X).1 (obj Y).1 ≤
        8 * DP.clusterMetric.radius X.1 Y.1 := by
  intro X Y b
  obtain ⟨hXY, hYX⟩ := scale_comparable_of_rep DP (X := X.1) (Y := Y.1) b
  obtain ⟨hXt, htX⟩ := scale_comparable_of_bridge DP DQ (X := X.1) (X' := (obj X).1)
    (bridge X) (hbridge X) (hβ X)
  obtain ⟨hYt, htY⟩ := scale_comparable_of_bridge DP DQ (X := Y.1) (X' := (obj Y).1)
    (bridge Y) (hbridge Y) (hβ Y)
  have hβX := hβ X
  have hβY := hβ Y
  have hρXY := hρ X Y
  have hn1 := min_le_left (DQ.scale (obj X).1) (DQ.scale (obj Y).1)
  have hn2 := min_le_right (DQ.scale (obj X).1) (DQ.scale (obj Y).1)
  show 2 * ρ X Y + 5 * β X + 5 * β Y + 2 * (2 * min (DP.scale X.1) (DP.scale Y.1)) +
      2 * min (DQ.scale (obj X).1) (DQ.scale (obj Y).1) ≤
    8 * (2 * min (DP.scale X.1) (DP.scale Y.1))
  rcases min_choice (DP.scale X.1) (DP.scale Y.1) with hm | hm
  · linarith
  · linarith

/-! ### The relative functor between scaled cluster groupoids -/

/-- **The relative cluster functor between scaled cluster groupoids** (Kun--Thom,
Lemma 4.3), at the improvement radius `improveRadius`. -/
noncomputable def scaledRelativeFunctor {I : Type u} {J : Type u'} [Fintype I] [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DP : ScaledPartialClusterSystem I L) (DQ : ScaledPartialClusterSystem J L)
    {R : Set I} {D : Set J} (obj : R → D)
    (bridge : ∀ X : R,
      FinitePartialBijection (DP.clusterMetric.model X.1) (DQ.clusterMetric.model (obj X).1))
    (β : R → ℕ)
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (hforward : ∀ (X Y : R) (b : DP.presentation.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) (DP.clusterMetric.val b)).equivarianceDefect
          (DQ.act (obj X).1) (DQ.act (obj Y).1)).card : ℝ) <
        DQ.K₀ * DQ.h * ((min (DQ.scale (obj X).1) (DQ.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hbackward : ∀ (X Y : R) (b : DP.presentation.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) (DP.clusterMetric.val b)).symm.equivarianceDefect
          (DQ.act (obj Y).1) (DQ.act (obj X).1)).card : ℝ) <
        DQ.K₀ * DQ.h * ((min (DQ.scale (obj X).1) (DQ.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hβ : ∀ X : R, 100 * β X ≤ DQ.scale (obj X).1)
    (hρ : ∀ X Y : R, 100 * improveRadius DQ obj X Y ≤ DQ.scale (obj X).1) :
    (DP.presentation.restrict R).Obj ⥤ (DQ.presentation.restrict D).Obj :=
  GroupoidPresentation.ClusterMetric.relativeFunctor DP.clusterMetric DQ.clusterMetric obj
    bridge β (improveRadius DQ obj) hbridge
    (himprove_of_defects DP.clusterMetric DQ obj bridge (improveRadius DQ obj) hforward
      hbackward (lt_improveRadius DQ obj))
    (respects_of_small DP DQ obj bridge β (improveRadius DQ obj) hbridge hβ hρ)
    (comp_of_small DP DQ obj bridge β (improveRadius DQ obj) hbridge hβ hρ)

/-- **Faithfulness** of the relative cluster functor between scaled cluster groupoids. -/
theorem scaledRelativeFunctor_faithful {I : Type u} {J : Type u'} [Fintype I] [Fintype J]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (DP : ScaledPartialClusterSystem I L) (DQ : ScaledPartialClusterSystem J L)
    {R : Set I} {D : Set J} (obj : R → D)
    (bridge : ∀ X : R,
      FinitePartialBijection (DP.clusterMetric.model X.1) (DQ.clusterMetric.model (obj X).1))
    (β : R → ℕ)
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (hforward : ∀ (X Y : R) (b : DP.presentation.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) (DP.clusterMetric.val b)).equivarianceDefect
          (DQ.act (obj X).1) (DQ.act (obj Y).1)).card : ℝ) <
        DQ.K₀ * DQ.h * ((min (DQ.scale (obj X).1) (DQ.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hbackward : ∀ (X Y : R) (b : DP.presentation.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) (DP.clusterMetric.val b)).symm.equivarianceDefect
          (DQ.act (obj Y).1) (DQ.act (obj X).1)).card : ℝ) <
        DQ.K₀ * DQ.h * ((min (DQ.scale (obj X).1) (DQ.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hβ : ∀ X : R, 100 * β X ≤ DQ.scale (obj X).1)
    (hρ : ∀ X Y : R, 100 * improveRadius DQ obj X Y ≤ DQ.scale (obj X).1) :
    (scaledRelativeFunctor DP DQ obj bridge β hbridge hforward hbackward hβ hρ).Faithful :=
  GroupoidPresentation.ClusterMetric.relativeFunctor_faithful DP.clusterMetric
    DQ.clusterMetric obj bridge β (improveRadius DQ obj) hbridge
    (himprove_of_defects DP.clusterMetric DQ obj bridge (improveRadius DQ obj) hforward
      hbackward (lt_improveRadius DQ obj))
    (respects_of_small DP DQ obj bridge β (improveRadius DQ obj) hbridge hβ hρ)
    (comp_of_small DP DQ obj bridge β (improveRadius DQ obj) hbridge hβ hρ)
    (faithful_of_small DP DQ obj bridge β (improveRadius DQ obj) hbridge hβ hρ)

end RelativeFunctorImprove
end GroupApproximation
