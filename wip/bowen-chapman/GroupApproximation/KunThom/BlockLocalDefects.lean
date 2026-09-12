import GroupApproximation.KunThom.RelativeFunctorEstimate
import GroupApproximation.Sofic.Asymptotics
import Mathlib.Tactic.Group

/-!
# Bridge defects summed over matched blocks

`BlockEmbedding.card_equivarianceDefect_bridge_le` bounds the equivariance defect
of one bridge by the conjugation failures of `q` over the whole model, so summing
it over many blocks counts every failure once per block.
`RelativeFunctorEstimate.card_equivarianceDefect_bridge_le_local` and
`RelativeFunctorEstimate.card_equivarianceDefect_symm_bridge_le_local` charge a
bridge only with the failures on its own block, through
`RelativeFunctorEstimate.conjFailure`.  This file sums those bounds over a set
`good` of blocks matched by a map `π` injective on `good`, for two labelled
actions `A` on the source blocks and `A'` on the target blocks.  Every
conjugation failure is then counted once, and the total is a Hamming
disagreement.

* `filter_labelFailure_eq_hammingDisagreement`: the points where `q` fails to
  carry `a s` to `a' s` are the disagreement of `q * a s` and `a' s * q`.
* `card_hammingDisagreement_inv_mul_eq`: `q⁻¹` fails to carry `a'` back to `a` at
  as many points.
* `BlockEmbedding.sum_card_conjFailure_le_hamming`,
  `BlockEmbedding.sum_card_conjFailure_inv_le_hamming` and
  `BlockEmbedding.sum_card_conjFailure_inv_comp_le_hamming`: the localized
  failures of `q` and of `q⁻¹`, summed over blocks, are at most the disagreement
  of `q * A.act s` and `A'.act s * q`.
* `BlockEmbedding.sum_card_equivarianceDefect_bridge_le_matched` and
  `BlockEmbedding.sum_card_symm_equivarianceDefect_bridge_le_matched`: over the
  blocks `i ∈ good`, the forward defects of the bridges realized by `q` from `i`
  to `π i`, and the backward defects of their reverses, are at most `|L|` times
  the unmatched mass plus, for every label, the compatibility failures of both
  block actions over all blocks and that disagreement, each counted once.
* `negligible_sum_card_equivarianceDefect_bridge_matched` and
  `negligible_sum_card_symm_equivarianceDefect_bridge_matched`: the sequential
  forms.

For a single labelled action and a permutation almost commuting with it,
`CentralizerBisectionRepresentationDefects` charges the bridge defects to
`BlockAction.localObstruction` instead.  The sum of the step 9 budget over
retained objects is `StepNineHammingSums`; the two Hamming lemmas bound its two
conjugation-failure totals by one disagreement.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

/-- **Conjugation failures as a Hamming disagreement.**  The points at which `q`
fails to carry `a s` to `a' s` are the points at which `q * a s` and `a' s * q`
disagree. -/
theorem filter_labelFailure_eq_hammingDisagreement {L : Type*} (q : Equiv.Perm Y)
    (a a' : L → Equiv.Perm Y) (s : L) :
    (Finset.univ.filter fun y : Y ↦ q (a s y) ≠ a' s (q y)) =
      hammingDisagreement (q * a s) (a' s * q) :=
  rfl

/-- **Failures of the inverse.**  `q⁻¹` fails to carry `a'` to `a` at as many
points as `q` fails to carry `a` to `a'`. -/
theorem card_hammingDisagreement_inv_mul_eq (q a a' : Equiv.Perm Y) :
    (hammingDisagreement (q⁻¹ * a') (a * q⁻¹)).card =
      (hammingDisagreement (q * a) (a' * q)).card := by
  rw [hammingDisagreement_eq_support, hammingDisagreement_eq_support]
  have e : (a * q⁻¹)⁻¹ * (q⁻¹ * a') = q * ((a' * q)⁻¹ * (q * a))⁻¹ * q⁻¹ := by group
  rw [e, Equiv.Perm.card_support_conj, Equiv.Perm.support_inv]

namespace BlockEmbedding

/-- **Localized failures of `q`.**  Summed over all blocks, the localized failures
of `q` at a label are at most the disagreement of `q * A.act s` and
`A'.act s * q`. -/
theorem sum_card_conjFailure_le_hamming [Fintype I] {L : Type*}
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (A A' : BlockAction E L) (s : L) :
    ∑ C, (RelativeFunctorEstimate.conjFailure E q A A' C s).card ≤
      (hammingDisagreement (q * A.act s) (A'.act s * q)).card :=
  RelativeFunctorEstimate.sum_card_conjFailure_le E q A A' s

/-- **Localized failures of `q⁻¹`.**  Summed over all blocks, the localized
failures of `q⁻¹` carrying `A'` back to `A` are at most the same disagreement. -/
theorem sum_card_conjFailure_inv_le_hamming [Fintype I] {L : Type*}
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (A A' : BlockAction E L) (s : L) :
    ∑ C, (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A C s).card ≤
      (hammingDisagreement (q * A.act s) (A'.act s * q)).card :=
  (RelativeFunctorEstimate.sum_card_conjFailure_le E q⁻¹ A' A s).trans
    (card_hammingDisagreement_inv_mul_eq q (A.act s) (A'.act s)).le

/-- **Localized failures of `q⁻¹` at matched blocks.**  For `π` injective on
`good`, the localized failures of `q⁻¹` on the blocks `π i` with `i ∈ good` are at
most the disagreement of `q * A.act s` and `A'.act s * q`. -/
theorem sum_card_conjFailure_inv_comp_le_hamming [Fintype I] {L : Type*}
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (A A' : BlockAction E L) (s : L)
    (good : Finset I) (π : I → I) (hπ : Set.InjOn π (good : Set I)) :
    ∑ i ∈ good, (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A (π i) s).card ≤
      (hammingDisagreement (q * A.act s) (A'.act s * q)).card := by
  classical
  calc ∑ i ∈ good, (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A (π i) s).card
      = ∑ C ∈ good.image π, (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A C s).card := by
        rw [Finset.sum_image hπ]
    _ ≤ ∑ C, (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A C s).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ (hammingDisagreement (q * A.act s) (A'.act s * q)).card :=
        E.sum_card_conjFailure_inv_le_hamming q A A' s

/-- **Forward bridge defects over matched blocks.**  Let `π` be injective on
`good`.  Over the blocks `i ∈ good`, the forward defects of the bridges realized
by `q` from `i` to `π i` are at most `|L|` times their unmatched mass plus, for
every label `s`, the compatibility failures of `A` and of `A'` over all blocks and
the disagreement of `q * A.act s` and `A'.act s * q`. -/
theorem sum_card_equivarianceDefect_bridge_le_matched [Fintype I] {L : Type*}
    [Fintype L] [DecidableEq L] (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (A A' : BlockAction E L) (good : Finset I) (π : I → I)
    (hπ : Set.InjOn π (good : Set I)) :
    ∑ i ∈ good, ((E.bridge q i (π i)).equivarianceDefect (A.blockAct i)
        (A'.blockAct (π i))).card ≤
      Fintype.card L * ∑ i ∈ good, (E.bridge q i (π i)).sourceDefect +
        ∑ s : L, (∑ C, (A.compatFailure C s).card +
          (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
          ∑ C, (A'.compatFailure C s).card) := by
  have hlabel : ∀ s : L, ∑ i ∈ good, ((E.bridge q i (π i)).sourceDefect +
        (A.compatFailure i s).card + (RelativeFunctorEstimate.conjFailure E q A A' i s).card +
        (A'.compatFailure (π i) s).card) ≤
      ∑ i ∈ good, (E.bridge q i (π i)).sourceDefect +
        (∑ C, (A.compatFailure C s).card +
          (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
          ∑ C, (A'.compatFailure C s).card) := by
    intro s
    have h₁ : ∑ i ∈ good, (A.compatFailure i s).card ≤ ∑ C, (A.compatFailure C s).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ good)
    have h₂ : ∑ i ∈ good, (RelativeFunctorEstimate.conjFailure E q A A' i s).card ≤
        ∑ C, (RelativeFunctorEstimate.conjFailure E q A A' C s).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ good)
    have h₃ := E.sum_card_conjFailure_le_hamming q A A' s
    have h₄ : ∑ i ∈ good, (A'.compatFailure (π i) s).card ≤
        ∑ C, (A'.compatFailure C s).card := by
      classical
      calc ∑ i ∈ good, (A'.compatFailure (π i) s).card
          = ∑ C ∈ good.image π, (A'.compatFailure C s).card := by rw [Finset.sum_image hπ]
        _ ≤ ∑ C, (A'.compatFailure C s).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    simp only [Finset.sum_add_distrib]
    omega
  calc ∑ i ∈ good, ((E.bridge q i (π i)).equivarianceDefect (A.blockAct i)
        (A'.blockAct (π i))).card
      ≤ ∑ i ∈ good, ∑ s : L, ((E.bridge q i (π i)).sourceDefect +
          (A.compatFailure i s).card + (RelativeFunctorEstimate.conjFailure E q A A' i s).card +
          (A'.compatFailure (π i) s).card) :=
        Finset.sum_le_sum fun i _ ↦
          RelativeFunctorEstimate.card_equivarianceDefect_bridge_le_local E q i (π i) A A'
    _ = ∑ s : L, ∑ i ∈ good, ((E.bridge q i (π i)).sourceDefect +
          (A.compatFailure i s).card + (RelativeFunctorEstimate.conjFailure E q A A' i s).card +
          (A'.compatFailure (π i) s).card) :=
        Finset.sum_comm
    _ ≤ ∑ s : L, (∑ i ∈ good, (E.bridge q i (π i)).sourceDefect +
          (∑ C, (A.compatFailure C s).card +
            (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
            ∑ C, (A'.compatFailure C s).card)) :=
        Finset.sum_le_sum fun s _ ↦ hlabel s
    _ = Fintype.card L * ∑ i ∈ good, (E.bridge q i (π i)).sourceDefect +
          ∑ s : L, (∑ C, (A.compatFailure C s).card +
            (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
            ∑ C, (A'.compatFailure C s).card) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Backward bridge defects over matched blocks.**  Let `π` be injective on
`good`.  Over the blocks `i ∈ good`, the backward defects of the reverses of the
bridges realized by `q` from `i` to `π i` are at most `|L|` times their missing
range mass plus, for every label `s`, the compatibility failures of `A'` and of
`A` over all blocks and the disagreement of `q * A.act s` and `A'.act s * q`. -/
theorem sum_card_symm_equivarianceDefect_bridge_le_matched [Fintype I] {L : Type*}
    [Fintype L] [DecidableEq L] (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (A A' : BlockAction E L) (good : Finset I) (π : I → I)
    (hπ : Set.InjOn π (good : Set I)) :
    ∑ i ∈ good, ((E.bridge q i (π i)).symm.equivarianceDefect (A'.blockAct (π i))
        (A.blockAct i)).card ≤
      Fintype.card L * ∑ i ∈ good, (E.bridge q i (π i)).targetDefect +
        ∑ s : L, (∑ C, (A'.compatFailure C s).card +
          (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
          ∑ C, (A.compatFailure C s).card) := by
  have hlabel : ∀ s : L, ∑ i ∈ good, ((E.bridge q i (π i)).targetDefect +
        (A'.compatFailure (π i) s).card +
        (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A (π i) s).card +
        (A.compatFailure i s).card) ≤
      ∑ i ∈ good, (E.bridge q i (π i)).targetDefect +
        (∑ C, (A'.compatFailure C s).card +
          (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
          ∑ C, (A.compatFailure C s).card) := by
    intro s
    have h₁ : ∑ i ∈ good, (A'.compatFailure (π i) s).card ≤
        ∑ C, (A'.compatFailure C s).card := by
      classical
      calc ∑ i ∈ good, (A'.compatFailure (π i) s).card
          = ∑ C ∈ good.image π, (A'.compatFailure C s).card := by rw [Finset.sum_image hπ]
        _ ≤ ∑ C, (A'.compatFailure C s).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h₂ := E.sum_card_conjFailure_inv_comp_le_hamming q A A' s good π hπ
    have h₃ : ∑ i ∈ good, (A.compatFailure i s).card ≤ ∑ C, (A.compatFailure C s).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ good)
    simp only [Finset.sum_add_distrib]
    omega
  calc ∑ i ∈ good, ((E.bridge q i (π i)).symm.equivarianceDefect (A'.blockAct (π i))
        (A.blockAct i)).card
      ≤ ∑ i ∈ good, ∑ s : L, ((E.bridge q i (π i)).targetDefect +
          (A'.compatFailure (π i) s).card +
          (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A (π i) s).card +
          (A.compatFailure i s).card) :=
        Finset.sum_le_sum fun i _ ↦
          RelativeFunctorEstimate.card_equivarianceDefect_symm_bridge_le_local E q i (π i) A A'
    _ = ∑ s : L, ∑ i ∈ good, ((E.bridge q i (π i)).targetDefect +
          (A'.compatFailure (π i) s).card +
          (RelativeFunctorEstimate.conjFailure E q⁻¹ A' A (π i) s).card +
          (A.compatFailure i s).card) :=
        Finset.sum_comm
    _ ≤ ∑ s : L, (∑ i ∈ good, (E.bridge q i (π i)).targetDefect +
          (∑ C, (A'.compatFailure C s).card +
            (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
            ∑ C, (A.compatFailure C s).card)) :=
        Finset.sum_le_sum fun s _ ↦ hlabel s
    _ = Fintype.card L * ∑ i ∈ good, (E.bridge q i (π i)).targetDefect +
          ∑ s : L, (∑ C, (A'.compatFailure C s).card +
            (hammingDisagreement (q * A.act s) (A'.act s * q)).card +
            ∑ C, (A.compatFailure C s).card) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]

end BlockEmbedding

/-- **Forward bridge defects over matched blocks, sequential form.**  Along a
sequence of models, suppose the unmatched mass of the matched bridges, the
compatibility failures of both labelled actions, and for every label the
disagreement of `q n * A.act s` and `A'.act s * q n` are negligible.  Then the
total forward defect of the matched bridges is negligible. -/
theorem negligible_sum_card_equivarianceDefect_bridge_matched {Y : ℕ → FiniteModel}
    {I : ℕ → Type u} [∀ n, Fintype (I n)] {L : Type*} [Fintype L] [DecidableEq L]
    (E : ∀ n, BlockEmbedding (Y n) (I n)) (q : ∀ n, Equiv.Perm (Y n))
    (A A' : ∀ n, BlockAction (E n) L) (good : ∀ n, Finset (I n)) (π : ∀ n, I n → I n)
    (hπ : ∀ n, Set.InjOn (π n) (good n : Set (I n)))
    (hunmatched : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ i ∈ good n, (((E n).bridge (q n) i (π n i)).sourceDefect : ℝ))
    (hcompat : ∀ s, Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ C, (((A n).compatFailure C s).card : ℝ))
    (hcompat' : ∀ s, Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ C, (((A' n).compatFailure C s).card : ℝ))
    (hconj : ∀ s, Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ((hammingDisagreement (q n * (A n).act s) ((A' n).act s * q n)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ good n, ((((E n).bridge (q n) i (π n i)).equivarianceDefect ((A n).blockAct i)
        ((A' n).blockAct (π n i))).card : ℝ) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ Finset.sum_nonneg fun i _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    ((hunmatched.const_mul (Fintype.card L : ℝ)).add
      (Negligible.sum Finset.univ _ fun s _ ↦ ((hcompat s).add (hconj s)).add (hcompat' s)))
  exact_mod_cast (E n).sum_card_equivarianceDefect_bridge_le_matched (q n) (A n) (A' n)
    (good n) (π n) (hπ n)

/-- **Backward bridge defects over matched blocks, sequential form.**  Along a
sequence of models, suppose the missing range mass of the matched bridges, the
compatibility failures of both labelled actions, and for every label the
disagreement of `q n * A.act s` and `A'.act s * q n` are negligible.  Then the
total backward defect of the reversed matched bridges is negligible. -/
theorem negligible_sum_card_symm_equivarianceDefect_bridge_matched {Y : ℕ → FiniteModel}
    {I : ℕ → Type u} [∀ n, Fintype (I n)] {L : Type*} [Fintype L] [DecidableEq L]
    (E : ∀ n, BlockEmbedding (Y n) (I n)) (q : ∀ n, Equiv.Perm (Y n))
    (A A' : ∀ n, BlockAction (E n) L) (good : ∀ n, Finset (I n)) (π : ∀ n, I n → I n)
    (hπ : ∀ n, Set.InjOn (π n) (good n : Set (I n)))
    (hunmatched : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ i ∈ good n, (((E n).bridge (q n) i (π n i)).targetDefect : ℝ))
    (hcompat : ∀ s, Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ C, (((A n).compatFailure C s).card : ℝ))
    (hcompat' : ∀ s, Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ C, (((A' n).compatFailure C s).card : ℝ))
    (hconj : ∀ s, Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ((hammingDisagreement (q n * (A n).act s) ((A' n).act s * q n)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ good n, ((((E n).bridge (q n) i (π n i)).symm.equivarianceDefect
        ((A' n).blockAct (π n i)) ((A n).blockAct i)).card : ℝ) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ Finset.sum_nonneg fun i _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    ((hunmatched.const_mul (Fintype.card L : ℝ)).add
      (Negligible.sum Finset.univ _ fun s _ ↦ ((hcompat' s).add (hconj s)).add (hcompat s)))
  exact_mod_cast (E n).sum_card_symm_equivarianceDefect_bridge_le_matched (q n) (A n) (A' n)
    (good n) (π n) (hπ n)

end BlockPatching
end GroupApproximation
