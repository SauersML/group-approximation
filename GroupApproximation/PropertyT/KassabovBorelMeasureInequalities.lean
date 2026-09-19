import GroupApproximation.PropertyT.KassabovMeasureInequalities
import Mathlib.MeasureTheory.Measure.Real

/-!
# Kassabov's inequalities for genuine finite measures

`KassabovMeasureInequalities` proves the numerical and finite-additive core of
Kassabov's disjoint transport argument.  This module supplies the interface
needed for an ordinary `MeasureTheory.Measure`.

Only measurable sets enter the quasi-invariance predicate.  Every use of exact
finite additivity carries measurability hypotheses for the pieces.  In
particular, this file neither declares all subsets measurable nor converts a
countably additive measure into an all-subset finitely additive structure.
The real mass of a measurable set is `mu.real A = (mu A).toReal`; finiteness of
`mu` ensures that this conversion loses no mass.
-/

namespace GroupApproximation

universe u v

namespace KassabovBorelMeasureInequalities

open MeasureTheory Set
open scoped BigOperators

open KassabovMeasureInequalities

variable {Omega : Type u} [MeasurableSpace Omega]

/-- Kassabov's quadratic quasi-invariance estimate for an ordinary finite
measure.  It is asserted only when both the source set and its image are
measurable. -/
def MeasurableQuasiInvariantAtScale (mu : Measure Omega) [IsFiniteMeasure mu]
    (epsilon : ℝ) (g : Omega → Omega) : Prop :=
  ∀ A : Set Omega, MeasurableSet A → MeasurableSet (g '' A) →
    |mu.real (g '' A) - mu.real A| ≤
      2 * epsilon * Real.sqrt (mu.real A) + epsilon ^ 2

/-- For a bijection, quadratic quasi-invariance in both directions implies
the square-root formulation of Kassabov's Lemma 2.4 on every measurable set
whose image is measurable. -/
theorem abs_sqrt_measureReal_image_sub_le
    (mu : Measure Omega) [IsFiniteMeasure mu] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (g : Equiv.Perm Omega)
    (hg : MeasurableQuasiInvariantAtScale mu epsilon g)
    (hginv : MeasurableQuasiInvariantAtScale mu epsilon g.symm)
    (A : Set Omega) (hA : MeasurableSet A)
    (himage : MeasurableSet (g '' A)) :
    |Real.sqrt (mu.real (g '' A)) - Real.sqrt (mu.real A)| ≤ epsilon := by
  have hforwardAbs := hg A hA himage
  have hforward :
      mu.real (g '' A) ≤ mu.real A +
        2 * epsilon * Real.sqrt (mu.real A) + epsilon ^ 2 := by
    linarith [le_abs_self (mu.real (g '' A) - mu.real A)]
  have hbackSet : g.symm '' (g '' A) = A := by
    ext x
    simp
  have hbackImage : MeasurableSet (g.symm '' (g '' A)) := by
    rw [hbackSet]
    exact hA
  have hbackAbs := hginv (g '' A) himage hbackImage
  rw [hbackSet] at hbackAbs
  have hback :
      mu.real A ≤ mu.real (g '' A) +
        2 * epsilon * Real.sqrt (mu.real (g '' A)) + epsilon ^ 2 := by
    linarith [le_abs_self (mu.real A - mu.real (g '' A))]
  have hle := sqrt_le_sqrt_add_of_le_add_two_mul_sqrt
    measureReal_nonneg measureReal_nonneg hepsilon hforward
  have hge := sqrt_le_sqrt_add_of_le_add_two_mul_sqrt
    measureReal_nonneg measureReal_nonneg hepsilon hback
  rw [abs_le]
  constructor <;> linarith

/-- **Measurable disjoint-union transport.**  Suppose the measurable sets
`A i` are pairwise disjoint, their measurable images under bijections `g i`
are pairwise disjoint and lie in `B`, and inverse transport obeys the
measurable quadratic quasi-invariance estimate.  Then

`sqrt (mu.real (⋃ i ∈ s, A i)) ≤
  sqrt (mu.real B) + sqrt (s.card) * epsilon`.

The proof uses `measureReal_biUnion_finset` twice.  Thus the two exact finite
union identities are obtained from countable additivity on measurable sets,
not from an all-subset finite-additivity surrogate. -/
theorem sqrt_measureReal_biUnion_le_of_disjoint_transport
    {I : Type v} (mu : Measure Omega) [IsFiniteMeasure mu]
    (s : Finset I) (A : I → Set Omega) (B : Set Omega)
    (g : I → Equiv.Perm Omega) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hA_measurable : ∀ i ∈ s, MeasurableSet (A i))
    (himage_measurable : ∀ i ∈ s, MeasurableSet (g i '' A i))
    (hA_disjoint : Set.Pairwise (↑s) fun i j ↦ Disjoint (A i) (A j))
    (himage_disjoint : Set.Pairwise (↑s) fun i j ↦
      Disjoint (g i '' A i) (g j '' A j))
    (himage_subset : (⋃ i ∈ s, g i '' A i) ⊆ B)
    (hquasi : ∀ i ∈ s,
      MeasurableQuasiInvariantAtScale mu epsilon (g i).symm) :
    Real.sqrt (mu.real (⋃ i ∈ s, A i)) ≤
      Real.sqrt (mu.real B) + Real.sqrt (s.card : ℝ) * epsilon := by
  classical
  have hmassA :
      mu.real (⋃ i ∈ s, A i) = ∑ i ∈ s, mu.real (A i) :=
    measureReal_biUnion_finset hA_disjoint hA_measurable
  have hmassImage :
      mu.real (⋃ i ∈ s, g i '' A i) =
        ∑ i ∈ s, mu.real (g i '' A i) :=
    measureReal_biUnion_finset himage_disjoint himage_measurable
  have himageMass : ∑ i ∈ s, mu.real (g i '' A i) ≤ mu.real B := by
    rw [← hmassImage]
    exact measureReal_mono himage_subset
  have htransport : ∀ i ∈ s,
      mu.real (A i) ≤ mu.real (g i '' A i) +
        2 * epsilon * Real.sqrt (mu.real (g i '' A i)) + epsilon ^ 2 := by
    intro i hi
    have hbackSet : (g i).symm '' (g i '' A i) = A i := by
      ext x
      simp
    have hbackMeasurable :
        MeasurableSet ((g i).symm '' (g i '' A i)) := by
      rw [hbackSet]
      exact hA_measurable i hi
    have hq := hquasi i hi (g i '' A i)
      (himage_measurable i hi) hbackMeasurable
    rw [hbackSet] at hq
    linarith [le_abs_self (mu.real (A i) - mu.real (g i '' A i))]
  rw [hmassA]
  exact sqrt_sum_le_sqrt_bound_add_sqrt_card_mul s
    (fun i ↦ mu.real (A i)) (fun i ↦ mu.real (g i '' A i))
    (mu.real B) epsilon
    (fun _ _ ↦ measureReal_nonneg)
    (fun _ _ ↦ measureReal_nonneg)
    himageMass measureReal_nonneg hepsilon htransport

end KassabovBorelMeasureInequalities

end GroupApproximation
