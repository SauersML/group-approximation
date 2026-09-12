import GroupApproximation.KunThom.StepNineHammingCandidates
import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBlockWords

/-!
# Step 9 over cluster frames: negligible budget totals

`BlockPatching.vanishing_hammingDistance_patch_conj` is the sequential form of the last
Hamming estimate in Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3).  It asks
the retained step 9 budgets to have negligible sum.
`BlockEmbedding.sum_stepNineBudget_le_of_candidates` bounds that sum by global totals.
This file shows the sum is negligible along a sequence of models once each total is.

* `sum_map_le_length_mul` and `sum_card_wordCompatFailure_le`: the compatibility
  failures of words of length at most `k` total at most `|L| · k` times those of the
  labels.
* `sum_targetDefect_bridge_le`: along a matching `π` injective on `D`, the missing range
  masses of the bridges realized by `q` from `j` to `π j` total at most their missing
  source masses plus the mass of the objects outside `D`.  The block sizes of `j` and
  `π j` cancel over the matching.
* `negligible_threshold_mul_card`: a vanishing threshold times the model size is
  negligible.
* `negligible_sum_stepNineBudget`: the retained budget has negligible sum.  The inputs
  are negligible totals of the two bridge terms, of the compatibility failures of every
  label, and of the conjugation failures of `q` and `q⁻¹`, candidate arrows at a
  vanishing threshold, and words of bounded length.
-/

namespace GroupApproximation
namespace CompressorHamming

open BlockPatching FinitePartialBijection

universe u

/-- A list of values each at most `B` sums to at most its length times `B`. -/
theorem sum_map_le_length_mul {α : Type*} (f : α → ℕ) (B : ℕ) (hB : ∀ x, f x ≤ B) :
    ∀ w : List α, (w.map f).sum ≤ w.length * B
  | [] => by simp
  | x :: w => by
      have ih := sum_map_le_length_mul f B hB w
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc f x + (w.map f).sum ≤ B + w.length * B := Nat.add_le_add (hB x) ih
        _ = (w.length + 1) * B := by ring

variable {Y : FiniteModel} {I : Type u}

/-- **Word compatibility totals.**  If every word has length at most `k`, the
compatibility failures of the words total at most `|L| · k` times the compatibility
failures of the labels. -/
theorem sum_card_wordCompatFailure_le [Fintype I] {L : Type*} [Fintype L]
    {E : BlockEmbedding Y I} (A : BlockAction E L) (ws : L → List L) (k : ℕ)
    (hk : ∀ s, (ws s).length ≤ k) :
    ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card ≤
      Fintype.card L * (k * ∑ C, ∑ l : L, (A.compatFailure C l).card) := by
  have hper : ∀ s C, (A.wordCompatFailure C (ws s)).card ≤
      k * ∑ l : L, (A.compatFailure C l).card := by
    intro s C
    have h₁ := A.card_wordCompatFailure_le C (ws s)
    have h₂ := sum_map_le_length_mul (fun l ↦ (A.compatFailure C l).card)
      (∑ l : L, (A.compatFailure C l).card)
      (fun l ↦ Finset.single_le_sum (f := fun l ↦ (A.compatFailure C l).card)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ l)) (ws s)
    have h₃ : (ws s).length * ∑ l : L, (A.compatFailure C l).card ≤
        k * ∑ l : L, (A.compatFailure C l).card :=
      Nat.mul_le_mul_right _ (hk s)
    exact h₁.trans (h₂.trans h₃)
  calc ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card
      ≤ ∑ s : L, ∑ C, k * ∑ l : L, (A.compatFailure C l).card :=
        Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun C _ ↦ hper s C
    _ = Fintype.card L * (k * ∑ C, ∑ l : L, (A.compatFailure C l).card) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum]

/-- **Missing range mass along a matching.**  For `π` injective on `D`, the missing
range masses of the bridges realized by `q` from `j` to `π j`, summed over `D`, are at
most their missing source masses plus the mass of the objects outside `D`. -/
theorem sum_targetDefect_bridge_le [Fintype I] [DecidableEq I] (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (π : I → I) (D : Finset I) (hπ : Set.InjOn π D) :
    ∑ j ∈ D, (E.bridge q j (π j)).targetDefect ≤
      ∑ j ∈ D, (E.bridge q j (π j)).sourceDefect +
        ∑ j ∈ Finset.univ \ D, Fintype.card (E.model j) := by
  have hper : ∀ j, (E.bridge q j (π j)).targetDefect + Fintype.card (E.model j) =
      (E.bridge q j (π j)).sourceDefect + Fintype.card (E.model (π j)) := by
    intro j
    have hst := (E.bridge q j (π j)).card_source_eq_card_target
    have hs : (E.bridge q j (π j)).source.card ≤ Fintype.card (E.model j) :=
      Finset.card_le_univ _
    have ht : (E.bridge q j (π j)).target.card ≤ Fintype.card (E.model (π j)) :=
      Finset.card_le_univ _
    unfold FinitePartialBijection.sourceDefect FinitePartialBijection.targetDefect
    omega
  have hsum : ∑ j ∈ D, (E.bridge q j (π j)).targetDefect + ∑ j ∈ D, Fintype.card (E.model j) =
      ∑ j ∈ D, (E.bridge q j (π j)).sourceDefect +
        ∑ j ∈ D, Fintype.card (E.model (π j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hper j
  have himage : ∑ j ∈ D, Fintype.card (E.model (π j)) ≤ ∑ C, Fintype.card (E.model C) :=
    sum_comp_le_sum_univ (fun C ↦ Fintype.card (E.model C)) π D hπ
  have hsplit : ∑ j ∈ Finset.univ \ D, Fintype.card (E.model j) +
      ∑ j ∈ D, Fintype.card (E.model j) = ∑ C, Fintype.card (E.model C) :=
    Finset.sum_sdiff (Finset.subset_univ D)
  omega

/-- A vanishing threshold times the model size is negligible, with any constant. -/
theorem negligible_threshold_mul_card {Y : ℕ → FiniteModel} (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n)
    (hvanish : Vanishing h) (c : ℝ) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      c * (h n / 34 * Fintype.card (Y n)) := by
  have hthreshold : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ h n / 34 * Fintype.card (Y n) := by
    refine Vanishing.squeeze (fun n ↦ ?_) (fun n ↦ ?_) (hvanish.const_mul (1 / 34))
    · exact div_nonneg (mul_nonneg (div_nonneg (hh n) (by norm_num))
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    · show h n / 34 * (Fintype.card (Y n) : ℝ) / Fintype.card (Y n) ≤ 1 / 34 * h n
      by_cases hcard : Fintype.card (Y n) = 0
      · rw [hcard, Nat.cast_zero, div_zero]
        exact mul_nonneg (by norm_num) (hh n)
      · have hpos : (0 : ℝ) < Fintype.card (Y n) := by
          exact_mod_cast Nat.pos_of_ne_zero hcard
        rw [mul_div_assoc, div_self hpos.ne', mul_one]
        linarith
  exact hthreshold.const_mul c

/-- **Negligible step 9 budget.**  Along a sequence of models, suppose the arrows of `α`
and `β` are cluster candidates at a vanishing threshold `h`, at scales of at most a
seventeenth of their blocks, and the words have length at most `k`.  If the two bridge
totals over the retained objects, the compatibility failures of every label, and the
conjugation failures of `q` and of `q⁻¹` are negligible, then so is the retained step 9
budget. -/
theorem negligible_sum_stepNineBudget {Y : ℕ → FiniteModel} {I : ℕ → Type u}
    [∀ n, Fintype (I n)] {L : Type*} [Fintype L] {E : ∀ n, BlockEmbedding (Y n) (I n)}
    (α β : ∀ n, BlockArrows (E n)) (q : ∀ n, Equiv.Perm (Y n))
    (A : ∀ n, BlockAction (E n) L) (ws : L → List L) (k : ℕ) (hk : ∀ s, (ws s).length ≤ k)
    (π : ∀ n, I n → I n) (good : ∀ n, Finset (I n)) (hπ : ∀ n, Set.InjOn (π n) (good n))
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hvanish : Vanishing h) (mα mβ : ∀ n, I n → ℕ)
    (hsizeα : ∀ n C, 17 * mα n C ≤ Fintype.card ((E n).model C))
    (hsizeβ : ∀ n C, 17 * mβ n C ≤ Fintype.card ((E n).model C))
    (hcandα : ∀ n C, ((α n).arrow C).IsClusterCandidate ((A n).blockAct C)
      ((A n).blockAct ((α n).objEquiv C)) (h n) (mα n C))
    (hcandβ : ∀ n C, ((β n).arrow C).IsClusterCandidate ((A n).blockAct C)
      ((A n).blockAct ((β n).objEquiv C)) (h n) (mβ n C))
    (hbridge : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ good n, (((E n).bridge (q n)⁻¹ (π n i) i).targetDefect : ℝ))
    (hbridge' : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ good n, (((E n).bridge (q n)⁻¹ ((β n).objEquiv (π n i))
        ((α n).objEquiv i)).sourceDefect : ℝ))
    (hcompat : ∀ s : L, Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ C, (((A n).compatFailure C s).card : ℝ))
    (hconj : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ((∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (q n) (A n)
        (RelativeFunctorEstimate.wordBlockAction (A n) ws) C s).card : ℕ) : ℝ))
    (hconj' : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ((∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (q n)⁻¹
        (RelativeFunctorEstimate.wordBlockAction (A n) ws) (A n) C s).card : ℕ) : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ good n, ((E n).stepNineBudget (α n) (β n) (q n) (A n) ws k (π n) i : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (Y n) := fun n ↦ Nat.cast_nonneg _
  have hcompatSum : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ s ∈ (Finset.univ : Finset L), ∑ C, (((A n).compatFailure C s).card : ℝ) :=
    Negligible.sum Finset.univ _ fun s _ ↦ hcompat s
  have hcompatSwap : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ C, ∑ s : L, (((A n).compatFailure C s).card : ℝ) :=
    hcompatSum.congr fun _ ↦ Finset.sum_comm
  have he := (hconj'.add ((((hbridge.const_mul (Fintype.card L : ℝ)).add
      (hbridge'.const_mul (Fintype.card L : ℝ))).add (hcompatSum.const_mul 2)).add
        (((hcompatSwap.const_mul (k : ℝ)).const_mul (Fintype.card L : ℝ)).const_mul 2) |>.add
          hconj)).add
    (negligible_threshold_mul_card h hh hvanish ((2 + Fintype.card L * k : ℕ) : ℝ))
  refine Negligible.mono_nonneg hN
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_) he
  have hlem := (E n).sum_stepNineBudget_le_of_candidates (α n) (β n) (q n) (A n) ws k (π n)
    (good n) (hπ n) (hh n) (mα n) (mβ n) (hsizeα n) (hsizeβ n) (hcandα n) (hcandβ n)
  have hword : ((∑ s : L, ∑ C, ((A n).wordCompatFailure C (ws s)).card : ℕ) : ℝ) ≤
      ((Fintype.card L * (k * ∑ C, ∑ l : L, ((A n).compatFailure C l).card) : ℕ) : ℝ) := by
    exact_mod_cast sum_card_wordCompatFailure_le (A n) ws k hk
  have hmul₁ : ∑ i ∈ good n, (Fintype.card L : ℝ) *
      (((E n).bridge (q n)⁻¹ (π n i) i).targetDefect : ℝ) =
      (Fintype.card L : ℝ) *
        ∑ i ∈ good n, (((E n).bridge (q n)⁻¹ (π n i) i).targetDefect : ℝ) := by
    rw [Finset.mul_sum]
  have hmul₂ : ∑ i ∈ good n, (Fintype.card L : ℝ) *
      (((E n).bridge (q n)⁻¹ ((β n).objEquiv (π n i)) ((α n).objEquiv i)).sourceDefect : ℝ) =
      (Fintype.card L : ℝ) * ∑ i ∈ good n,
        (((E n).bridge (q n)⁻¹ ((β n).objEquiv (π n i)) ((α n).objEquiv i)).sourceDefect :
          ℝ) := by
    rw [Finset.mul_sum]
  push_cast at hlem hword ⊢
  linarith

end CompressorHamming
end GroupApproximation
