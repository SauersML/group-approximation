import GroupApproximation.KunThom.RelativeFunctorScaled
import Mathlib.Data.Real.Archimedean

/-!
# Improving transported representatives for the relative cluster functor

`ScaledPartialClusterSystem.relativeClusterFunctor` (Kun--Thom, arXiv:2608.06222v3,
Lemma 4.3) takes the hypothesis `himprove`: every representative, transported through
the bridges at its two objects, lies within `ρ X Y` of a representative between the
matched objects.  It also asks `100 ρ X Y ≤ min (scale X) (scale Y)` for every pair.
This file produces both from small equivariance defects of the transported maps.

* `himprove_of_defects`: a transported representative whose forward and backward
  equivariance defects are below `K₀ h min (scale X) (scale Y) / 2` at the matched
  objects is repaired by `ScaledPartialClusterSystem.repair_spec` into a representative
  within `d |model X|` of it.
* `improveRadius`: `⌊d |model (obj X)|⌋₊ + 1` on pairs joined by a representative, and
  `0` on the other pairs, where `himprove` asks nothing.  It exceeds the distance bound
  of the repair (`lt_improveRadius`), and it is at most `min (scale X) (scale Y) / 100`
  once `0 ≤ d ≤ 1 / 5000`, retained scales are at least `400` and matched scales agree
  within `11 / 10` (`hundred_mul_improveRadius_le`).
* `relativeClusterFunctorOfDefects`: the bundle of Lemma 4.3 at `improveRadius`, from
  the defect bounds, the bridge masses and the scale conditions.

The radius comes from the distance bound `d |model X|` of the repair rather than from
the pair radius `2 min (scale X) (scale Y)`, so it is small against the scales.  A radius
depending on the source object alone would fail the pair condition on pairs of very
different sizes, which is why it is set to `0` where no representative joins the pair.
-/

namespace GroupApproximation
namespace RelativeFunctorImprove

open FinitePartialBijection GroupoidPresentation

universe u

/-! ### Improvement from small defects -/

/-- **Improvement of transported representatives.**  If the transport of every
representative through the bridges has forward and backward equivariance defects below
`K₀ h min (scale X') (scale Y') / 2` at the matched objects `X'`, `Y'`, then its repair
is a representative between the matched objects within `d |model X'|` of it, hence
within any radius above that bound. -/
theorem himprove_of_defects {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I}
    (obj : R → S)
    (bridge : ∀ X : R, FinitePartialBijection (D.model X.1) (D.model (obj X).1))
    (ρ : R → R → ℕ)
    (hforward : ∀ (X Y : R) (b : D.clusterData.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) b.1).equivarianceDefect
          (D.act (obj X).1) (D.act (obj Y).1)).card : ℝ) <
        D.K₀ * D.h * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hbackward : ∀ (X Y : R) (b : D.clusterData.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) b.1).symm.equivarianceDefect
          (D.act (obj Y).1) (D.act (obj X).1)).card : ℝ) <
        D.K₀ * D.h * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) / 2)
    (hρ : ∀ (X Y : R), D.clusterData.Rep X.1 Y.1 →
      D.d * Fintype.card (D.model (obj X).1) < ρ X Y) :
    ∀ (X Y : R) (b : D.clusterData.Rep X.1 Y.1),
      ∃ r : D.clusterData.Rep (obj X).1 (obj Y).1,
        r.1.twoSidedDisagreement (sandwich (bridge X) (bridge Y) b.1) < ρ X Y := by
  intro X Y b
  obtain ⟨hcand, -, hdist⟩ := D.repair_spec (sandwich (bridge X) (bridge Y) b.1)
    (hforward X Y b) (hbackward X Y b)
  refine ⟨⟨D.repair (sandwich (bridge X) (bridge Y) b.1),
    (mem_clusterCandidates (D.act (obj X).1) (D.act (obj Y).1) D.h
      (min (D.scale (obj X).1) (D.scale (obj Y).1)) _).mpr hcand⟩, ?_⟩
  have hlt : (((D.repair (sandwich (bridge X) (bridge Y) b.1)).twoSidedDisagreement
      (sandwich (bridge X) (bridge Y) b.1) : ℕ) : ℝ) < ρ X Y :=
    hdist.trans_lt (hρ X Y b)
  exact_mod_cast hlt

/-! ### The improvement radius -/

open Classical in
/-- The improvement radius of a pair of retained objects: one more than the integer part
of the distance bound `d |model (obj X)|` when some representative joins the pair, and
`0` otherwise. -/
noncomputable def improveRadius {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I}
    (obj : R → S) (X Y : R) : ℕ :=
  if Nonempty (D.clusterData.Rep X.1 Y.1) then
    ⌊D.d * Fintype.card (D.model (obj X).1)⌋₊ + 1
  else 0

/-- On a pair joined by a representative, the improvement radius exceeds the distance
bound of the repair. -/
theorem lt_improveRadius {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I}
    (obj : R → S) {X Y : R} (b : D.clusterData.Rep X.1 Y.1) :
    D.d * Fintype.card (D.model (obj X).1) < improveRadius D obj X Y := by
  have h := Nat.lt_floor_add_one (D.d * (Fintype.card (D.model (obj X).1) : ℝ))
  unfold improveRadius
  split_ifs with hne
  · exact_mod_cast h
  · exact absurd (Nonempty.intro b) hne

/-- Once `0 ≤ d ≤ 1 / 5000`, every retained scale is at least `400` and matched scales
agree within `11 / 10`, the improvement radius of every pair is at most a hundredth of
the smaller scale. -/
theorem hundred_mul_improveRadius_le {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I}
    (obj : R → S) (hd0 : 0 ≤ D.d) (hd : D.d ≤ 1 / 5000)
    (hscale : ∀ X : R, 400 ≤ D.scale X.1)
    (hobj : ∀ X : R, 10 * D.scale X.1 ≤ 11 * D.scale (obj X).1 ∧
      10 * D.scale (obj X).1 ≤ 11 * D.scale X.1) (X Y : R) :
    100 * improveRadius D obj X Y ≤ min (D.scale X.1) (D.scale Y.1) := by
  unfold improveRadius
  split_ifs with hne
  · obtain ⟨b⟩ := hne
    obtain ⟨hXY, -⟩ := D.scale_comparable_of_rep b
    obtain ⟨hXo, hoX⟩ := hobj X
    have hsX := hscale X
    have hsY := hscale Y
    have heq := D.scale_eq (obj X).1
    have hcardNat : Fintype.card (D.model (obj X).1) ≤ 19 * D.scale (obj X).1 := by
      omega
    have hcard : (Fintype.card (D.model (obj X).1) : ℝ) ≤ 19 * (D.scale (obj X).1 : ℝ) := by
      exact_mod_cast hcardNat
    have hfloor : (⌊D.d * Fintype.card (D.model (obj X).1)⌋₊ : ℝ) ≤
        D.d * Fintype.card (D.model (obj X).1) :=
      Nat.floor_le (mul_nonneg hd0 (Nat.cast_nonneg _))
    have hmul : D.d * Fintype.card (D.model (obj X).1) ≤
        1 / 5000 * (Fintype.card (D.model (obj X).1) : ℝ) :=
      mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
    have hreal : (5000 : ℝ) * (⌊D.d * Fintype.card (D.model (obj X).1)⌋₊ : ℝ) ≤
        19 * (D.scale (obj X).1 : ℝ) := by
      linarith
    have hnat : 5000 * ⌊D.d * Fintype.card (D.model (obj X).1)⌋₊ ≤
        19 * D.scale (obj X).1 := by
      exact_mod_cast hreal
    have hm₁ := min_le_left (D.scale X.1) (D.scale Y.1)
    have hm₂ := min_le_right (D.scale X.1) (D.scale Y.1)
    have hm₃ := min_choice (D.scale X.1) (D.scale Y.1)
    omega
  · omega

/-! ### The relative cluster functor from small defects -/

/-- **Kun–Thom, Lemma 4.3, on a scaled cluster system, from small defects.**  The
bundle `ScaledPartialClusterSystem.relativeClusterFunctor` at the radius `improveRadius`.
Its inputs are the matching and the bridges; the defect bounds of the transported
representatives; bridge masses at most a hundredth of the scales; matched scales within
`11 / 10`; the distance factor `0 ≤ d ≤ 1 / 5000`; and retained scales at least `400`. -/
noncomputable def relativeClusterFunctorOfDefects {I : Type u} [Fintype I] {L : Type*}
    [Fintype L] [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L)
    {R S : Finset I} (π : I → I) (hmaps : Set.MapsTo π S R) (hinj : Set.InjOn π S)
    (hsurj : Set.SurjOn π S R)
    (bridge : ∀ X : (R : Set I), FinitePartialBijection (D.model X.1)
      (D.model (ClusterMetric.matchingInverse π hsurj X).1))
    (β : ↥(R : Set I) → ℕ)
    (hbridge : ∀ X : (R : Set I), (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (hforward : ∀ (X Y : (R : Set I)) (b : D.clusterData.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) b.1).equivarianceDefect
          (D.act (ClusterMetric.matchingInverse π hsurj X).1)
          (D.act (ClusterMetric.matchingInverse π hsurj Y).1)).card : ℝ) <
        D.K₀ * D.h * ((min (D.scale (ClusterMetric.matchingInverse π hsurj X).1)
          (D.scale (ClusterMetric.matchingInverse π hsurj Y).1) : ℕ) : ℝ) / 2)
    (hbackward : ∀ (X Y : (R : Set I)) (b : D.clusterData.Rep X.1 Y.1),
      (((sandwich (bridge X) (bridge Y) b.1).symm.equivarianceDefect
          (D.act (ClusterMetric.matchingInverse π hsurj Y).1)
          (D.act (ClusterMetric.matchingInverse π hsurj X).1)).card : ℝ) <
        D.K₀ * D.h * ((min (D.scale (ClusterMetric.matchingInverse π hsurj X).1)
          (D.scale (ClusterMetric.matchingInverse π hsurj Y).1) : ℕ) : ℝ) / 2)
    (hβ : ∀ X : (R : Set I), 100 * β X ≤ D.scale X.1)
    (hobj : ∀ X : (R : Set I),
      10 * D.scale X.1 ≤ 11 * D.scale (ClusterMetric.matchingInverse π hsurj X).1 ∧
        10 * D.scale (ClusterMetric.matchingInverse π hsurj X).1 ≤ 11 * D.scale X.1)
    (hd0 : 0 ≤ D.d) (hd : D.d ≤ 1 / 5000)
    (hscale : ∀ X : (R : Set I), 400 ≤ D.scale X.1) :
    D.presentation.RelativeClusterFunctor R S :=
  D.relativeClusterFunctor π hmaps hinj hsurj bridge β
    (improveRadius D (ClusterMetric.matchingInverse π hsurj)) hbridge
    (himprove_of_defects D (ClusterMetric.matchingInverse π hsurj) bridge
      (improveRadius D (ClusterMetric.matchingInverse π hsurj)) hforward hbackward
      (fun _ _ b ↦ lt_improveRadius D (ClusterMetric.matchingInverse π hsurj) b))
    hβ
    (hundred_mul_improveRadius_le D (ClusterMetric.matchingInverse π hsurj) hd0 hd hscale
      hobj)
    hobj

end RelativeFunctorImprove
end GroupApproximation
