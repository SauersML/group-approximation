import GroupApproximation.KunThom.StepNineHammingReference
import GroupApproximation.KunThom.RelativeFunctorEstimate
import GroupApproximation.KunThom.FixedPointNormalizationSummation

/-!
# Step 9: the Hamming estimate of Kun--Thom Theorem 4.1

Kun and Thom (arXiv:2608.06222v3, tex lines 1314--1338) end the proof of
Theorem 4.1 with

`d_H(b̂_n, u_n â_n u_n⁻¹) ≤ χ_n + r_n + 2 q_n + O(δ_n + ε_n)`.

Here `â_n` patches a bisection representing the almost centralizing sequence,
`b̂_n` patches the bisection built from the relative functor, and `u_n`
represents a compressor.  The distance gap of the cluster groupoid only says that
two arrows in one cluster disagree on a bounded fraction of a block, and that
does not sum to `o(|Y_n|)`.  So the estimate here separates again, block by
block, at a scale proportional to the actual equivariance defects of the two
arrows compared and to the label edit budget of the block.  The cluster radius
enters only through the near bound `hnear`.

* `BlockArrows.card_hammingDisagreement_patch_conj_le_budget`: take arbitrary
  reference arrows realizing `q⁻¹ · β.patch · q`, with combined defect at most
  `budget i` on a retained object `i`.  Then `β.patch` disagrees with
  `q · α.patch · q⁻¹` on at most the mass off the glued domain of `α`, plus
  `Σ_retained (2 · edit i + 4 · budget i) / cheeger`, plus the full exceptional
  blocks.
* `BlockEmbedding.stepNineBudget` and
  `BlockArrows.card_hammingDisagreement_patch_conj_le_stepNine`: the same bound
  with the raw maps of the relative functor as references, i.e. the arrows
  `b_{π i}` transported through the bridges realized by `q⁻¹`.  The budget is
  `#defect(a_i)` plus the bound
  `RelativeFunctorEstimate.card_equivarianceDefect_sandwich_bridge_words_le`.
* `vanishing_hammingDistance_patch_conj`: the sequential `Vanishing` form.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

namespace BlockArrows

variable {E : BlockEmbedding Y I}

/-- **Step 9 with actual defects.**  Every retained object `i` carries:
* a reference arrow `c i` realizing `q⁻¹ · β.patch · q`;
* a block action that expands with constant `cheeger / 4` at every scale above
  twice its edit budget;
* a bound `budget i` on the combined equivariance defect of `α.arrow i` and `c i`.

If the two arrows are near and the block has room, then `β.patch` disagrees with
`q · α.patch · q⁻¹` on at most the mass off the glued domain of `α`, plus
`(2 · edit i + 4 · budget i) / cheeger` per retained object, plus the full
exceptional blocks. -/
theorem card_hammingDisagreement_patch_conj_le_budget [Fintype I] [DecidableEq I]
    {L : Type*} [Fintype L] [DecidableEq L]
    (α β : BlockArrows E) (q : Equiv.Perm Y) (A : BlockAction E L) (good : Finset I)
    (c : ∀ i, FinitePartialBijection (E.model i) (E.model (α.objEquiv i)))
    (hc : ∀ i ∈ good, α.RealizesOn (q⁻¹ * β.patch * q) i (c i))
    {cheeger : ℝ} (hcheeger : 0 < cheeger) (edit budget : I → ℝ) (sc : I → ℕ)
    (hedit : ∀ i ∈ good, 0 ≤ edit i)
    (hexp : ∀ i ∈ good, ∀ m : ℕ, edit i < cheeger * m / 2 →
      HasTaggedExpansionAtScale (A.blockAct i) (cheeger / 4) m)
    (hbudget : ∀ i ∈ good,
      ((((α.arrow i).equivarianceDefect (A.blockAct i) (A.blockAct (α.objEquiv i))).card +
        ((c i).equivarianceDefect (A.blockAct i) (A.blockAct (α.objEquiv i))).card : ℕ) : ℝ) ≤
          budget i)
    (hnear : ∀ i ∈ good, ((α.arrow i).disagreement (c i)).card < 2 * sc i)
    (hroom : ∀ i ∈ good, (2 * sc i : ℝ) + (2 * edit i + 4 * budget i) / cheeger + 1 ≤
      Fintype.card (E.model i)) :
    ((hammingDisagreement β.patch (q * α.patch * q⁻¹)).card : ℝ) ≤
      ((Finset.univ \ α.domain).card : ℝ) +
        ∑ i ∈ good, (2 * edit i + 4 * budget i) / cheeger +
        ∑ i ∈ goodᶜ, (Fintype.card (E.model i) : ℝ) := by
  have hbnn : ∀ i ∈ good, 0 ≤ budget i := fun i hi ↦
    (Nat.cast_nonneg _).trans (hbudget i hi)
  have hkey : ∀ i ∈ good, 2 * edit i + 4 * budget i <
      cheeger * ((⌊(2 * edit i + 4 * budget i) / cheeger⌋₊ + 1 : ℕ) : ℝ) := by
    intro i _
    have hfl := Nat.lt_floor_add_one ((2 * edit i + 4 * budget i) / cheeger)
    have hlt := mul_lt_mul_of_pos_left hfl hcheeger
    have hcancel : cheeger * ((2 * edit i + 4 * budget i) / cheeger) =
        2 * edit i + 4 * budget i :=
      mul_div_cancel₀ _ hcheeger.ne'
    push_cast
    linarith
  rw [card_hammingDisagreement_conj_swap]
  refine α.card_hammingDisagreement_patch_le_reseparation (q⁻¹ * β.patch * q) good c hc
    A.blockAct (fun i ↦ A.blockAct (α.objEquiv i)) (cheeger / 4)
    (fun i ↦ (2 * edit i + 4 * budget i) / cheeger) sc
    (fun i hi ↦ div_nonneg (by linarith [hedit i hi, hbnn i hi]) hcheeger.le)
    (fun i hi ↦ hexp i hi _ (by linarith [hkey i hi, hbnn i hi]))
    (fun i hi ↦ by linarith [hkey i hi, hbudget i hi, hedit i hi])
    hnear (fun i hi ↦ ?_)
  have hfloor : (⌊(2 * edit i + 4 * budget i) / cheeger⌋₊ : ℝ) ≤
      (2 * edit i + 4 * budget i) / cheeger :=
    Nat.floor_le (div_nonneg (by linarith [hedit i hi, hbnn i hi]) hcheeger.le)
  have hreal : ((2 * sc i + (⌊(2 * edit i + 4 * budget i) / cheeger⌋₊ + 1) : ℕ) : ℝ) ≤
      (Fintype.card (E.model i) : ℝ) := by
    push_cast
    linarith [hroom i hi]
  exact_mod_cast hreal

end BlockArrows

namespace BlockEmbedding

/-- **The step 9 budget of an object.**  The budget is the defect of the arrow
`a_i = α.arrow i` plus the defect bound of the raw map of the relative functor on
`b_{π i} = β.arrow (π i)`, from
`RelativeFunctorEstimate.card_equivarianceDefect_sandwich_bridge_words_le`.  That
bound has three parts:
* over all labels, the missing range mass of the bridge realized by `q⁻¹` from
  `π i` to `i`, the compatibility failures of the labels at `i` and of the words
  at `π i`, and the failures of `q` to carry a label into its word on `i`;
* `|L|` times the source defect plus `k` times the defect of `b_{π i}`;
* over all labels, the missing source mass of the bridge realized by `q⁻¹` from
  the image block of `π i` to the image block of `i`, the compatibility failures
  of the words there and of the labels at the image of `i`, and the failures of
  `q⁻¹` to carry a word into its label. -/
noncomputable def stepNineBudget {L : Type*} [Fintype L] (E : BlockEmbedding Y I)
    (α β : BlockArrows E) (q : Equiv.Perm Y) (A : BlockAction E L) (ws : L → List L)
    (k : ℕ) (π : I → I) (i : I) : ℕ :=
  ((α.arrow i).equivarianceDefect (A.blockAct i) (A.blockAct (α.objEquiv i))).card +
    (∑ s : L, ((E.bridge q⁻¹ (π i) i).targetDefect + (A.compatFailure i s).card +
        (RelativeFunctorEstimate.conjFailure E q A
          (RelativeFunctorEstimate.wordBlockAction A ws) i s).card +
        (A.wordCompatFailure (π i) (ws s)).card) +
      Fintype.card L * ((β.arrow (π i)).sourceDefect +
        k * ((β.arrow (π i)).equivarianceDefect (A.blockAct (π i))
          (A.blockAct (β.objEquiv (π i)))).card) +
      ∑ s : L, ((E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)).sourceDefect +
        (A.wordCompatFailure (β.objEquiv (π i)) (ws s)).card +
        (RelativeFunctorEstimate.conjFailure E q⁻¹
          (RelativeFunctorEstimate.wordBlockAction A ws) A (β.objEquiv (π i)) s).card +
        (A.compatFailure (α.objEquiv i) s).card))

/-- The combined defect of `a_i` and of the raw map of the relative functor on
`b_{π i}` is at most the step 9 budget of `i`. -/
theorem card_equivarianceDefect_le_stepNineBudget {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (α β : BlockArrows E) (q : Equiv.Perm Y) (A : BlockAction E L)
    (ws : L → List L) {k : ℕ} (hk : ∀ s, (ws s).length ≤ k) (π : I → I) (i : I) :
    ((α.arrow i).equivarianceDefect (A.blockAct i) (A.blockAct (α.objEquiv i))).card +
        ((sandwich (E.bridge q⁻¹ (π i) i) (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i))
          (β.arrow (π i))).equivarianceDefect (A.blockAct i)
            (A.blockAct (α.objEquiv i))).card ≤
      E.stepNineBudget α β q A ws k π i := by
  have h := RelativeFunctorEstimate.card_equivarianceDefect_sandwich_bridge_words_le E q⁻¹
    (π i) i (β.objEquiv (π i)) (α.objEquiv i) A ws hk (β.arrow (π i))
  rw [inv_inv] at h
  unfold stepNineBudget
  omega

end BlockEmbedding

namespace BlockArrows

variable {E : BlockEmbedding Y I}

/-- **Step 9 with the raw maps of the relative functor.**  On a retained object
`i` the reference arrow is `b_{π i}` transported back through the bridges realized
by `q⁻¹`, and the budget is `BlockEmbedding.stepNineBudget`. -/
theorem card_hammingDisagreement_patch_conj_le_stepNine [Fintype I] [DecidableEq I]
    {L : Type*} [Fintype L] [DecidableEq L]
    (α β : BlockArrows E) (q : Equiv.Perm Y) (A : BlockAction E L) (ws : L → List L)
    {k : ℕ} (hk : ∀ s, (ws s).length ≤ k) (π : I → I) (good : Finset I)
    {cheeger : ℝ} (hcheeger : 0 < cheeger) (edit : I → ℝ) (sc : I → ℕ)
    (hedit : ∀ i ∈ good, 0 ≤ edit i)
    (hexp : ∀ i ∈ good, ∀ m : ℕ, edit i < cheeger * m / 2 →
      HasTaggedExpansionAtScale (A.blockAct i) (cheeger / 4) m)
    (hnear : ∀ i ∈ good, ((α.arrow i).disagreement
      (sandwich (E.bridge q⁻¹ (π i) i) (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i))
        (β.arrow (π i)))).card < 2 * sc i)
    (hroom : ∀ i ∈ good, (2 * sc i : ℝ) +
      (2 * edit i + 4 * (E.stepNineBudget α β q A ws k π i : ℝ)) / cheeger + 1 ≤
        Fintype.card (E.model i)) :
    ((hammingDisagreement β.patch (q * α.patch * q⁻¹)).card : ℝ) ≤
      ((Finset.univ \ α.domain).card : ℝ) +
        ∑ i ∈ good, (2 * edit i + 4 * (E.stepNineBudget α β q A ws k π i : ℝ)) / cheeger +
        ∑ i ∈ goodᶜ, (Fintype.card (E.model i) : ℝ) :=
  α.card_hammingDisagreement_patch_conj_le_budget β q A good
    (fun i ↦ sandwich (E.bridge q⁻¹ (π i) i)
      (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)) (β.arrow (π i)))
    (fun i _ ↦ E.realizesOn_sandwich_bridge_inv α β q (π i) i) hcheeger edit
    (fun i ↦ (E.stepNineBudget α β q A ws k π i : ℝ)) sc hedit hexp
    (fun i _ ↦ by
      exact_mod_cast E.card_equivarianceDefect_le_stepNineBudget α β q A ws hk π i)
    hnear hroom

end BlockArrows

/-- **Step 9, sequential form.**  Suppose that along a sequence of models four
quantities are negligible against the model sizes: the mass off the glued domains,
the exceptional blocks, the retained edit budgets and the retained defect budgets.
Then the patched bisections `β n` and the conjugated patches `q n · α n · (q n)⁻¹`
have vanishing Hamming distance. -/
theorem vanishing_hammingDistance_patch_conj {Y : ℕ → FiniteModel} {I : ℕ → Type u}
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] {L : Type*} [Fintype L] [DecidableEq L]
    {E : ∀ n, BlockEmbedding (Y n) (I n)} (α β : ∀ n, BlockArrows (E n))
    (q : ∀ n, Equiv.Perm (Y n)) (A : ∀ n, BlockAction (E n) L) (good : ∀ n, Finset (I n))
    (c : ∀ n i, FinitePartialBijection ((E n).model i) ((E n).model ((α n).objEquiv i)))
    (hc : ∀ n, ∀ i ∈ good n, (α n).RealizesOn ((q n)⁻¹ * (β n).patch * q n) i (c n i))
    {cheeger : ℝ} (hcheeger : 0 < cheeger) (edit budget : ∀ n, I n → ℝ)
    (sc : ∀ n, I n → ℕ)
    (hedit : ∀ n, ∀ i ∈ good n, 0 ≤ edit n i)
    (hexp : ∀ n, ∀ i ∈ good n, ∀ m : ℕ, edit n i < cheeger * m / 2 →
      HasTaggedExpansionAtScale ((A n).blockAct i) (cheeger / 4) m)
    (hbudget : ∀ n, ∀ i ∈ good n,
      (((((α n).arrow i).equivarianceDefect ((A n).blockAct i)
          ((A n).blockAct ((α n).objEquiv i))).card +
        ((c n i).equivarianceDefect ((A n).blockAct i)
          ((A n).blockAct ((α n).objEquiv i))).card : ℕ) : ℝ) ≤ budget n i)
    (hnear : ∀ n, ∀ i ∈ good n, (((α n).arrow i).disagreement (c n i)).card < 2 * sc n i)
    (hroom : ∀ n, ∀ i ∈ good n,
      (2 * sc n i : ℝ) + (2 * edit n i + 4 * budget n i) / cheeger + 1 ≤
        Fintype.card ((E n).model i))
    (hoff : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ((Finset.univ \ (α n).domain).card : ℝ))
    (hexc : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ i ∈ (good n)ᶜ, (Fintype.card ((E n).model i) : ℝ))
    (heditSum : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ i ∈ good n, edit n i)
    (hbudgetSum : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ))
      fun n ↦ ∑ i ∈ good n, budget n i) :
    Vanishing fun n ↦ hammingDistance (Y n) (β n).patch (q n * (α n).patch * (q n)⁻¹) := by
  have hcard : ∀ n,
      ((hammingDisagreement (β n).patch (q n * (α n).patch * (q n)⁻¹)).card : ℝ) ≤
        ((Finset.univ \ (α n).domain).card : ℝ) +
          (2 / cheeger * ∑ i ∈ good n, edit n i + 4 / cheeger * ∑ i ∈ good n, budget n i) +
          ∑ i ∈ (good n)ᶜ, (Fintype.card ((E n).model i) : ℝ) := by
    intro n
    have h := (α n).card_hammingDisagreement_patch_conj_le_budget (β n) (q n) (A n)
      (good n) (c n) (hc n) hcheeger (edit n) (budget n) (sc n) (hedit n) (hexp n)
      (hbudget n) (hnear n) (hroom n)
    have hsplit : ∑ i ∈ good n, (2 * edit n i + 4 * budget n i) / cheeger =
        2 / cheeger * ∑ i ∈ good n, edit n i + 4 / cheeger * ∑ i ∈ good n, budget n i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    linarith
  exact vanishing_hammingDistance_of_card_le (fun n ↦ (β n).patch)
    (fun n ↦ q n * (α n).patch * (q n)⁻¹) _ hcard
    ((hoff.add ((heditSum.const_mul (2 / cheeger)).add
      (hbudgetSum.const_mul (4 / cheeger)))).add hexc)

end BlockPatching
end GroupApproximation
