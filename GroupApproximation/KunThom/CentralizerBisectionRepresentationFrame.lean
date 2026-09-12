import GroupApproximation.KunThom.CentralizerBisectionRepresentationScaledPatch
import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrame

/-!
# The forward half of Kun--Thom Lemma 4.2(4) on a cluster frame

`seqNormalizes_of_compressor_of_frameSteps` leaves `hrep` open: for a cluster frame
with a vanishing threshold, a sequence `v` almost commuting with `A(Γ)` is close to the
patched permutations of some sequence of total bisections.  This file proves it, given
that three error sequences are `o(threshold · |Y|)`:
* the uncovered mass of the frame;
* the commutation failures of `v` with the generator labels;
* the compatibility failures of the block actions.

* `ClusterFrame.repBound F v n`: an explicit bound on the disagreement of the
  representing patch with `v n`, in terms of those three quantities, the threshold and
  the Cheeger constant of the component family.
* `card_hammingDisagreement_patch_le_repBound`: every bisection completing the selected
  arrows of `v n` has patch within `repBound F v n` of `v n`.  It combines
  `BlockPatching.mul_card_hammingDisagreement_scaledBisectionPatch_le` with the charge
  totals.
* `negligible_repBound`: the bound is `o(|Y|)`.
* `ClusterFrame.exists_bis_patch_close`: the sequential statement, with bisections chosen
  by `BlockPatching.exists_bisection_selected`.

`CentralizerBisectionRepresentationFrameRetained` states it with the error sequences of the
retained components, which dominate those of the frame from its start index.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

open CentralizerNormalizationImprove BlockPatching CategoryTheory

namespace ClusterFrame

open Classical

/-- The explicit bound on the disagreement of the representing patch at index `n`. -/
noncomputable def repBound {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (v : ∀ n, Equiv.Perm (A.model n)) (n : ℕ) : ℝ :=
  ((F.embedding n).uncovered.card : ℝ) +
    (1 + 2 / R.data.family.cheeger) / 36 * (F.threshold n * Fintype.card (A.model n)) +
    (2 * Fintype.card ↥R.data.generators / R.data.family.cheeger ^ 2 +
        79 / R.data.family.cheeger) *
      (R.data.family.cheeger * ((F.embedding n).uncovered.card : ℝ) +
        2 * (F.action n).commutationMass (v n) + 5 * (F.action n).compatMass) +
    2 / R.data.family.cheeger *
      ((F.action n).commutationMass (v n) + 2 * (F.action n).compatMass) +
    152 * Fintype.card ↥R.data.generators / R.data.family.cheeger *
      ((R.data.family.cheeger * ((F.embedding n).uncovered.card : ℝ) +
        2 * (F.action n).commutationMass (v n) + 5 * (F.action n).compatMass) /
          F.threshold n) +
    152 * (((F.action n).commutationMass (v n) + 2 * (F.action n).compatMass) / F.threshold n)

/-- **The representing patch at one index.** -/
theorem card_hammingDisagreement_patch_le_repBound {G : Type} [Group G]
    {A : SoficApproximation G} {K : Type} [Group K] {ι : K →* G}
    {R : RetainedComponents A K ι} (F : ClusterFrame R) (v : ∀ n, Equiv.Perm (A.model n))
    (n : ℕ) (b : F.Bis n)
    (hb : ∀ X (hX : X ∈ selectedObjects (F.system n) (F.embedAt n) (F.embedAt_injective n)
        (F.embedAt_disjoint n) (v n)),
      ∃ e : b.objEquiv X = selectedObjectTarget (F.system n) (F.embedAt n)
          (F.embedAt_injective n) (F.embedAt_disjoint n) (v n) X,
        b.hom X ≫ eqToHom e = selectedArrow (F.system n) (F.embedAt n) (F.embedAt_injective n)
          (F.embedAt_disjoint n) (v n) X hX) :
    ((hammingDisagreement (v n) (F.patch n b)).card : ℝ) ≤ F.repBound v n := by
  have hc : 0 < R.data.family.cheeger := R.data.family.cheeger_pos
  have hh : 0 < F.threshold n := F.threshold_pos n
  have hexp : ∀ X : F.Obj n,
      FinitePartialBijection.HasTaggedExpansionAtScale ((F.system n).act X)
        R.data.family.cheeger 1 := fun X ↦
    hasTaggedExpansionAtScale_of_cheeger ((restrictFrom R.data.family F.start).expands n X) hc
      le_rfl 1
  have master := mul_card_hammingDisagreement_scaledBisectionPatch_le (F.system n) (F.embedAt n)
    (F.embedAt_injective n) (F.embedAt_disjoint n) (fun s ↦ A.map n (ι (s : K))) (v n) b hb hc
    hexp
  have master' : R.data.family.cheeger * R.data.family.cheeger * F.threshold n *
      ((hammingDisagreement (F.patch n b) (v n)).card : ℝ) ≤
      R.data.family.cheeger * R.data.family.cheeger * F.threshold n *
          ((F.embedding n).uncovered.card : ℝ) +
        (R.data.family.cheeger * R.data.family.cheeger * F.threshold n +
            2 * R.data.family.cheeger * F.threshold n) *
          (F.threshold n / 36 * Fintype.card (A.model n)) +
        2 * F.threshold n * (Fintype.card ↥R.data.generators *
            ∑ X, (F.action n).pieceCharge (v n) R.data.family.cheeger X +
          R.data.family.cheeger * ∑ X, (F.action n).obstructionMass (v n) X) +
        R.data.family.cheeger *
          ((F.threshold n + 38 * (F.threshold n + 2 * Fintype.card ↥R.data.generators)) *
              ∑ X, (F.action n).pieceCharge (v n) R.data.family.cheeger X +
            (2 * F.threshold n + 38 * (F.threshold n + 2 * Fintype.card ↥R.data.generators)) *
              ∑ X, (F.action n).pieceCharge (v n)⁻¹ R.data.family.cheeger X +
            2 * 38 * R.data.family.cheeger * (∑ X, (F.action n).obstructionMass (v n) X +
              ∑ X, (F.action n).obstructionMass (v n)⁻¹ X)) :=
    master
  have hsymm : (hammingDisagreement (F.patch n b) (v n)).card =
      (hammingDisagreement (v n) (F.patch n b)).card := by
    congr 1
    ext y
    simp only [mem_hammingDisagreement, ne_eq, ne_comm]
  rw [hsymm] at master'
  have hPC := (F.action n).sum_pieceCharge_le (v n) hc.le
  have hPC' := (F.action n).sum_pieceCharge_le (v n)⁻¹ hc.le
  rw [BlockAction.commutationMass_inv] at hPC'
  have hO := (F.action n).sum_obstructionMass_le (v n)
  have hO' := (F.action n).sum_obstructionMass_le (v n)⁻¹
  rw [BlockAction.commutationMass_inv] at hO'
  have hL : (0 : ℝ) ≤ Fintype.card ↥R.data.generators := Nat.cast_nonneg _
  have hk₁ : 0 ≤ 2 * F.threshold n * Fintype.card ↥R.data.generators := by positivity
  have hk₂ : 0 ≤ 2 * F.threshold n * R.data.family.cheeger := by positivity
  have hk₃ : 0 ≤ R.data.family.cheeger *
      (F.threshold n + 38 * (F.threshold n + 2 * Fintype.card ↥R.data.generators)) := by
    positivity
  have hk₄ : 0 ≤ R.data.family.cheeger *
      (2 * F.threshold n + 38 * (F.threshold n + 2 * Fintype.card ↥R.data.generators)) := by
    positivity
  have hk₅ : 0 ≤ R.data.family.cheeger * (2 * 38 * R.data.family.cheeger) := by positivity
  have q₁ := mul_le_mul_of_nonneg_left hPC hk₁
  have q₂ := mul_le_mul_of_nonneg_left hO hk₂
  have q₃ := mul_le_mul_of_nonneg_left hPC hk₃
  have q₄ := mul_le_mul_of_nonneg_left hPC' hk₄
  have q₅ := mul_le_mul_of_nonneg_left hO hk₅
  have q₆ := mul_le_mul_of_nonneg_left hO' hk₅
  have hpos : 0 < R.data.family.cheeger * R.data.family.cheeger * F.threshold n := by positivity
  have hident : R.data.family.cheeger * R.data.family.cheeger * F.threshold n * F.repBound v n =
      R.data.family.cheeger * R.data.family.cheeger * F.threshold n *
          ((F.embedding n).uncovered.card : ℝ) +
        (R.data.family.cheeger * R.data.family.cheeger * F.threshold n +
            2 * R.data.family.cheeger * F.threshold n) *
          (F.threshold n / 36 * Fintype.card (A.model n)) +
        2 * F.threshold n * Fintype.card ↥R.data.generators *
          (R.data.family.cheeger * ((F.embedding n).uncovered.card : ℝ) +
            2 * (F.action n).commutationMass (v n) + 5 * (F.action n).compatMass) +
        2 * F.threshold n * R.data.family.cheeger *
          ((F.action n).commutationMass (v n) + 2 * (F.action n).compatMass) +
        (R.data.family.cheeger *
            (F.threshold n + 38 * (F.threshold n + 2 * Fintype.card ↥R.data.generators)) +
          R.data.family.cheeger *
            (2 * F.threshold n + 38 * (F.threshold n + 2 * Fintype.card ↥R.data.generators))) *
          (R.data.family.cheeger * ((F.embedding n).uncovered.card : ℝ) +
            2 * (F.action n).commutationMass (v n) + 5 * (F.action n).compatMass) +
        2 * (R.data.family.cheeger * (2 * 38 * R.data.family.cheeger)) *
          ((F.action n).commutationMass (v n) + 2 * (F.action n).compatMass) := by
    unfold repBound
    have hcne : R.data.family.cheeger ≠ 0 := hc.ne'
    have hhne : F.threshold n ≠ 0 := hh.ne'
    field_simp
    ring
  refine le_of_mul_le_mul_left ?_ hpos
  rw [hident]
  linarith

/-- **The bound is negligible.** -/
theorem negligible_repBound {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (v : ∀ n, Equiv.Perm (A.model n))
    (hunc : Vanishing fun n ↦
      ((F.embedding n).uncovered.card : ℝ) / Fintype.card (A.model n) / F.threshold n)
    (hcomm : Vanishing fun n ↦
      (F.action n).commutationMass (v n) / Fintype.card (A.model n) / F.threshold n)
    (hcompat : Vanishing fun n ↦
      (F.action n).compatMass / Fintype.card (A.model n) / F.threshold n)
    (hthr : Vanishing F.threshold) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (F.repBound v) := by
  have hh : ∀ n, 0 < F.threshold n := F.threshold_pos
  have hh1 : ∀ n, F.threshold n ≤ 1 := fun n ↦ (F.threshold_small n).trans (by norm_num)
  have hCM : ∀ n, 0 ≤ (F.action n).commutationMass (v n) := fun n ↦
    Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hPM : ∀ n, 0 ≤ (F.action n).compatMass := fun n ↦
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hY : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  -- a nonnegative sequence dominated after division by the threshold
  have hdrop : ∀ (e : ℕ → ℝ), (∀ n, 0 ≤ e n) →
      (Vanishing fun n ↦ e n / Fintype.card (A.model n) / F.threshold n) →
        Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) e := by
    intro e he hv
    refine Vanishing.squeeze (fun n ↦ div_nonneg (he n) (hY n)) (fun n ↦ ?_) hv
    exact le_div_self (div_nonneg (he n) (hY n)) (hh n) (hh1 n)
  have hdiv : ∀ (e : ℕ → ℝ),
      (Vanishing fun n ↦ e n / Fintype.card (A.model n) / F.threshold n) →
        Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦ e n / F.threshold n := by
    intro e hv
    refine hv.congr fun n ↦ ?_
    show e n / (Fintype.card (A.model n) : ℝ) / F.threshold n =
      e n / F.threshold n / Fintype.card (A.model n)
    ring
  have hU := F.uncovered_negligible
  have hCMn := hdrop _ hCM hcomm
  have hPMn := hdrop _ hPM hcompat
  have hT : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ F.threshold n * Fintype.card (A.model n) := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg (mul_nonneg (hh n).le (hY n)) (hY n))
      (fun n ↦ ?_) hthr
    show F.threshold n * (Fintype.card (A.model n) : ℝ) / Fintype.card (A.model n) ≤
      F.threshold n
    by_cases hcard : Fintype.card (A.model n) = 0
    · rw [hcard, Nat.cast_zero, div_zero]
      exact (hh n).le
    · have hpos : (0 : ℝ) < Fintype.card (A.model n) := by
        exact_mod_cast Nat.pos_of_ne_zero hcard
      rw [mul_div_assoc, div_self hpos.ne', mul_one]
  have hP : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      R.data.family.cheeger * ((F.embedding n).uncovered.card : ℝ) +
        2 * (F.action n).commutationMass (v n) + 5 * (F.action n).compatMass :=
    ((hU.const_mul _).add (hCMn.const_mul 2)).add (hPMn.const_mul 5)
  have hO : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      (F.action n).commutationMass (v n) + 2 * (F.action n).compatMass :=
    hCMn.add (hPMn.const_mul 2)
  have hPh : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      (R.data.family.cheeger * ((F.embedding n).uncovered.card : ℝ) +
        2 * (F.action n).commutationMass (v n) + 5 * (F.action n).compatMass) /
          F.threshold n := by
    refine hdiv _ ?_
    refine (((hunc.const_mul R.data.family.cheeger).add (hcomm.const_mul 2)).add
      (hcompat.const_mul 5)).congr fun n ↦ ?_
    ring
  have hOh : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((F.action n).commutationMass (v n) + 2 * (F.action n).compatMass) / F.threshold n := by
    refine hdiv _ ?_
    refine (hcomm.add (hcompat.const_mul 2)).congr fun n ↦ ?_
    ring
  exact (((((hU.add (hT.const_mul _)).add (hP.const_mul _)).add (hO.const_mul _)).add
    (hPh.const_mul _)).add (hOh.const_mul 152)).congr fun n ↦ rfl

/-- **Kun--Thom Lemma 4.2(4), forward half, on a cluster frame.** -/
theorem exists_bis_patch_close {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (v : ∀ n, Equiv.Perm (A.model n))
    (hunc : Vanishing fun n ↦
      ((F.embedding n).uncovered.card : ℝ) / Fintype.card (A.model n) / F.threshold n)
    (hcomm : Vanishing fun n ↦
      (F.action n).commutationMass (v n) / Fintype.card (A.model n) / F.threshold n)
    (hcompat : Vanishing fun n ↦
      (F.action n).compatMass / Fintype.card (A.model n) / F.threshold n)
    (hthr : Vanishing F.threshold) :
    ∃ a : ∀ n, F.Bis n,
      Vanishing fun n ↦ hammingDistance (A.model n) (v n) (F.patch n (a n)) := by
  choose a ha using fun n ↦ exists_bisection_selected (F.system n) (F.embedAt n)
    (F.embedAt_injective n) (F.embedAt_disjoint n) (v n)
  exact ⟨a, vanishing_hammingDistance_of_card_le v (fun n ↦ F.patch n (a n)) (F.repBound v)
    (fun n ↦ F.card_hammingDisagreement_patch_le_repBound v n (a n) (ha n))
    (F.negligible_repBound v hunc hcomm hcompat hthr)⟩

end ClusterFrame

end CompressorNormalizationAssembly
end GroupApproximation
