import GroupApproximation.KunThom.CentralizerBisectionRepresentationFrame
import GroupApproximation.KunThom.CompressorNormalizationAssemblyDecomposition

/-!
# The forward half of Kun--Thom Lemma 4.2(4) from the retained components

`ClusterFrame.exists_bis_patch_close` asks the uncovered mass, the commutation
failures and the compatibility failures of the frame to be `o(threshold · |Y|)`.  From
its start index the frame is covered by the retained components, so these quantities
are dominated by those of the retained components, which `generatorDefect` adds up.

* `generatorDefect_eq_masses`: `generatorDefect R v n` is the uncovered mass, the
  commutation mass of `v n` and the compatibility mass of the retained components, over
  `|Y|`.
* `ClusterFrame.exists_bis_patch_close_of_retained`: for a frame with a vanishing
  threshold, if `generatorDefect R v = o(threshold)`, some sequence of total bisections
  has patched permutations close to `v`.  This is `hrep` in
  `seqNormalizes_of_compressor_of_frameSteps` and `seqNormalizes_distinguished_of_steps`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

open CentralizerNormalizationImprove BlockPatching

/-- The generator defect in terms of the masses of the retained block action. -/
theorem generatorDefect_eq_masses {G : Type} [Group G] {K : Type} [Group K]
    {A : SoficApproximation G} {ι : K →* G} (R : RetainedComponents A K ι)
    (v : ∀ n, Equiv.Perm (A.model n)) (n : ℕ) :
    generatorDefect R v n = (((R.data.embedding n).uncovered.card : ℝ) +
      (R.data.blockAction n).commutationMass (v n) + (R.data.blockAction n).compatMass) /
        Fintype.card (A.model n) := by
  have h1 : (R.data.blockAction n).commutationMass (v n) / Fintype.card (A.model n) =
      ∑ s ∈ R.data.generators,
        hammingDistance (A.model n) (v n * A.map n (ι s)) (A.map n (ι s) * v n) := by
    rw [BlockAction.commutationMass, Finset.sum_div,
      ← Finset.sum_coe_sort (s := R.data.generators)]
    rfl
  have h2 : (R.data.blockAction n).compatMass / Fintype.card (A.model n) =
      ∑ s : ↥R.data.generators,
        (∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ)) /
          Fintype.card (A.model n) := by
    rw [BlockAction.compatMass, Finset.sum_div]
  rw [generatorDefect, add_div, add_div, h1, h2]
  ring

namespace ClusterFrame

open Classical

/-- **Kun--Thom Lemma 4.2(4), forward half, from the retained components.** -/
theorem exists_bis_patch_close_of_retained {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (hthr : Vanishing F.threshold) (v : ∀ n, Equiv.Perm (A.model n))
    (hdom : Vanishing fun n ↦ generatorDefect R v n / F.threshold n) :
    ∃ a : ∀ n, F.Bis n,
      Vanishing fun n ↦ hammingDistance (A.model n) (v n) (F.patch n (a n)) := by
  have hh : ∀ n, 0 < F.threshold n := F.threshold_pos
  have hY : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  have hCM : ∀ n, 0 ≤ (R.data.blockAction n).commutationMass (v n) := fun n ↦
    Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hPM : ∀ n, 0 ≤ (R.data.blockAction n).compatMass := fun n ↦
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hUR : ∀ n, (0 : ℝ) ≤ ((R.data.embedding n).uncovered.card : ℝ) := fun n ↦
    Nat.cast_nonneg _
  -- the frame quantities are dominated by the retained ones from the start index on
  have hstep : ∀ (e : ℕ → ℝ), (∀ n, 0 ≤ e n) → (∀ n, F.start ≤ n → e n ≤
      ((R.data.embedding n).uncovered.card : ℝ) + (R.data.blockAction n).commutationMass (v n) +
        (R.data.blockAction n).compatMass) →
      Vanishing fun n ↦ e n / Fintype.card (A.model n) / F.threshold n := by
    intro e he hle
    refine Vanishing.squeeze_eventually hdom F.start fun n hn ↦ ⟨?_, ?_⟩
    · exact div_nonneg (div_nonneg (he n) (hY n)) (hh n).le
    · rw [generatorDefect_eq_masses]
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hle n hn) (hY n))
        (hh n).le
  have hunc := hstep (fun n ↦ ((F.embedding n).uncovered.card : ℝ))
    (fun n ↦ Nat.cast_nonneg (α := ℝ) _) fun n hn ↦ by
      show ((F.embedding n).uncovered.card : ℝ) ≤ _
      have hsub : ((F.embedding n).uncovered.card : ℝ) ≤
          ((R.data.embedding n).uncovered.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (F.uncovered_subset n hn)
      linarith [hCM n, hPM n]
  have hcomm := hstep (fun n ↦ (F.action n).commutationMass (v n))
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) fun n _ ↦ by
      show (F.action n).commutationMass (v n) ≤ _
      have heq : (F.action n).commutationMass (v n) =
          (R.data.blockAction n).commutationMass (v n) := rfl
      linarith [hUR n, hPM n]
  have hcompat := hstep (fun n ↦ (F.action n).compatMass)
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    fun n _ ↦ by
      show (F.action n).compatMass ≤ _
      have hle : (F.action n).compatMass ≤ (R.data.blockAction n).compatMass :=
        Finset.sum_le_sum fun s _ ↦ sum_subtype_val_le (F.start ≤ n)
          (fun i ↦ (((R.data.blockAction n).compatFailure i s).card : ℝ))
          (fun _ ↦ Nat.cast_nonneg _)
      linarith [hUR n, hCM n]
  exact F.exists_bis_patch_close v hunc hcomm hcompat hthr

end ClusterFrame

end CompressorNormalizationAssembly
end GroupApproximation
