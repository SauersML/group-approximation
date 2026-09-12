import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrame
import GroupApproximation.KunThom.CountingEndgameProps
import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBlockWords

/-!
# Step 9 over a cluster frame: word compatibility and bridge range masses

Two totals of the step 9 budget in Kun and Thom's proof of Theorem 4.1
(arXiv:2608.06222v3), over a cluster frame `F`.

* `negligible_sum_card_wordCompatFailure`: for words `ws s` in the generators, the
  compatibility failures of the block actions of the words have negligible total.
  - A word fails only where one of its letters fails
    (`BlockAction.card_wordCompatFailure_le`).
  - There are finitely many words, so their lengths are bounded.
  - Every label has negligible compatibility failures (`ClusterFrame.compat_negligible`).
* `negligible_sum_bridge_targetDefect`: for relative data `M` of a compressor `t`, the
  missing range masses of the bridges realized by `A(t)` from the matched objects `i` to
  their matches `π i` have negligible total.  A bridge is a bijection, so
  `targetDefect + |Q_i| = sourceDefect + |Q_{π i}|`.  Over the matching the block sizes
  cancel up to the unmatched weight.  The total is therefore at most the missing source
  masses (`M.bridge_negligible`) plus the weight of the unmatched objects
  (`M.unmatched_negligible`).
-/

namespace GroupApproximation
namespace StepNineHammingFrame

open BlockPatching CompressorNormalizationAssembly FinitePartialBijection

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

/-- **Word compatibility totals.**  If every word has length at most `k`, the
compatibility failures of the words total at most `|L| · k` times the compatibility
failures of the labels. -/
theorem sum_card_wordCompatFailure_le {Y : FiniteModel} {I : Type u} [Fintype I] {L : Type*}
    [Fintype L] {E : BlockEmbedding Y I} (A : BlockAction E L) (ws : L → List L) (k : ℕ)
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
theorem sum_targetDefect_bridge_le {Y : FiniteModel} {I : Type u} [Fintype I] [DecidableEq I]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (π : I → I) (D : Finset I)
    (hπ : Set.InjOn π D) :
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
    calc ∑ j ∈ D, Fintype.card (E.model (π j))
        = ∑ C ∈ D.image π, Fintype.card (E.model C) := (Finset.sum_image hπ).symm
      _ ≤ ∑ C, Fintype.card (E.model C) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hsplit : ∑ j ∈ Finset.univ \ D, Fintype.card (E.model j) +
      ∑ j ∈ D, Fintype.card (E.model j) = ∑ C, Fintype.card (E.model C) :=
    Finset.sum_sdiff (Finset.subset_univ D)
  omega

variable {G : Type} [Group G] {A : SoficApproximation G} {K : Type} [Group K] {ι : K →* G}
  {R : RetainedComponents A K ι}

open Classical in
/-- **Word compatibility failures on a frame.**  For any words in the generators, the
compatibility failures of the block actions of the words have negligible total. -/
theorem negligible_sum_card_wordCompatFailure (F : ClusterFrame R)
    (ws : ↥R.data.generators → List ↥R.data.generators) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((∑ s : ↥R.data.generators, ∑ X, ((F.action n).wordCompatFailure X (ws s)).card : ℕ) :
        ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  have hk : ∀ s, (ws s).length ≤
      (Finset.univ : Finset ↥R.data.generators).sup fun s ↦ (ws s).length := fun s ↦
    Finset.le_sup (f := fun s ↦ (ws s).length) (Finset.mem_univ s)
  have hcompatSum : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ s ∈ (Finset.univ : Finset ↥R.data.generators),
        ∑ X, (((F.action n).compatFailure X s).card : ℝ) :=
    Negligible.sum Finset.univ _ fun s _ ↦ F.compat_negligible s
  have hcompatSwap : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X, ∑ s : ↥R.data.generators, (((F.action n).compatFailure X s).card : ℝ) :=
    hcompatSum.congr fun _ ↦ Finset.sum_comm
  refine Negligible.mono_nonneg hN (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    ((hcompatSwap.const_mul
      (((Finset.univ : Finset ↥R.data.generators).sup fun s ↦ (ws s).length : ℕ) : ℝ)).const_mul
        (Fintype.card ↥R.data.generators : ℝ))
  have h := sum_card_wordCompatFailure_le (F.action n) ws _ hk
  have hR : ((∑ s : ↥R.data.generators, ∑ X, ((F.action n).wordCompatFailure X (ws s)).card :
      ℕ) : ℝ) ≤
      ((Fintype.card ↥R.data.generators *
        (((Finset.univ : Finset ↥R.data.generators).sup fun s ↦ (ws s).length) *
          ∑ X, ∑ l : ↥R.data.generators, ((F.action n).compatFailure X l).card) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hR
  exact hR

open Classical in
/-- **Missing range masses of the matching bridges.**  For relative data `M` of a
compressor `t`, the missing range masses of the bridges realized by `A(t)` from every
matched object to its match have negligible total. -/
theorem negligible_sum_bridge_targetDefect (F : ClusterFrame R) {t : G}
    (M : CountingEndgame.CompressorRelativeData t F) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ M.matched t n, (((F.embedding n).bridge (A.map n t) i
        ((M.functor t M.mem_compressors n).π i)).targetDefect : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  refine Negligible.mono_nonneg hN (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_) ((M.bridge_negligible t M.mem_compressors).add
      (M.unmatched_negligible t M.mem_compressors))
  have h := sum_targetDefect_bridge_le (F.embedding n) (A.map n t)
    (M.functor t M.mem_compressors n).π (M.matched t n)
    (M.functor t M.mem_compressors n).injOn
  have hR : ((∑ i ∈ M.matched t n, ((F.embedding n).bridge (A.map n t) i
        ((M.functor t M.mem_compressors n).π i)).targetDefect : ℕ) : ℝ) ≤
      ((∑ i ∈ M.matched t n, ((F.embedding n).bridge (A.map n t) i
          ((M.functor t M.mem_compressors n).π i)).sourceDefect +
        ∑ i ∈ Finset.univ \ M.matched t n, Fintype.card ((F.embedding n).model i) : ℕ) :
          ℝ) := by
    exact_mod_cast h
  push_cast at hR
  exact hR

end StepNineHammingFrame
end GroupApproximation
