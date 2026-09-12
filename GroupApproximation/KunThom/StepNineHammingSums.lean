import GroupApproximation.KunThom.StepNineHammingEstimate

/-!
# Step 9: summing the budget over retained objects

`BlockEmbedding.stepNineBudget` is a per-object quantity, and the sequential
form `vanishing_hammingDistance_patch_conj` needs its sum over the retained
objects to be negligible.  This file bounds that sum by totals that the matching,
labelling and bisection lanes control.

* `sum_comp_le_sum_univ`: a sum over retained objects, reindexed along a map
  injective on them, is at most the sum over all objects.
* `BlockEmbedding.sum_stepNineBudget_le`: for `π` injective on the retained
  objects, the retained budget is at most the sum of:
  - the retained bridge terms;
  - the total defect of the arrows of `α`;
  - twice the total compatibility failures of the labels, and twice those of the words;
  - the total localized conjugation failures of `q` and of `q⁻¹`;
  - `|L| · (sourceDefect + k · #defect)` summed over all arrows of `β`.

Both bridge terms are bounded by the retained matching error, through
`RelativeFunctorEstimate.sourceDefect_add_targetDefect_bridge_inv_le_objectImage`.
The conjugation failures of all blocks add up to the ambient failures, through
`RelativeFunctorEstimate.sum_card_conjFailure_le`.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

/-- A sum over retained objects, reindexed along a map injective on them, is at
most the sum over all objects. -/
theorem sum_comp_le_sum_univ [Fintype I] (f : I → ℕ) (g : I → I) (good : Finset I)
    (hg : Set.InjOn g good) :
    ∑ i ∈ good, f (g i) ≤ ∑ C, f C := by
  classical
  calc ∑ i ∈ good, f (g i) = ∑ C ∈ good.image g, f C := (Finset.sum_image hg).symm
    _ ≤ ∑ C, f C := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

namespace BlockEmbedding

/-- **The step 9 budget over retained objects.**  Let `π` be injective on the
retained objects.  The retained budget is then at most the sum of:
* the retained bridge terms;
* the total defect of the arrows of `α`;
* twice the total compatibility failures of the labels, and twice those of the words;
* the total conjugation failures of `q` and of `q⁻¹`;
* `|L| · (sourceDefect + k · #defect)` summed over all arrows of `β`. -/
theorem sum_stepNineBudget_le [Fintype I] {L : Type*} [Fintype L] (E : BlockEmbedding Y I)
    (α β : BlockArrows E) (q : Equiv.Perm Y) (A : BlockAction E L) (ws : L → List L)
    (k : ℕ) (π : I → I) (good : Finset I) (hπ : Set.InjOn π good) :
    ∑ i ∈ good, E.stepNineBudget α β q A ws k π i ≤
      ∑ i ∈ good, Fintype.card L * (E.bridge q⁻¹ (π i) i).targetDefect +
        ∑ i ∈ good, Fintype.card L *
          (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)).sourceDefect +
        ∑ i, ((α.arrow i).equivarianceDefect (A.blockAct i)
          (A.blockAct (α.objEquiv i))).card +
        2 * ∑ s : L, ∑ C, (A.compatFailure C s).card +
        2 * ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card +
        ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q A
          (RelativeFunctorEstimate.wordBlockAction A ws) C s).card +
        ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q⁻¹
          (RelativeFunctorEstimate.wordBlockAction A ws) A C s).card +
        ∑ C, Fintype.card L * ((β.arrow C).sourceDefect +
          k * ((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card) := by
  have hpoint : ∀ i, E.stepNineBudget α β q A ws k π i =
      Fintype.card L * (E.bridge q⁻¹ (π i) i).targetDefect +
        Fintype.card L * (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)).sourceDefect +
        ((α.arrow i).equivarianceDefect (A.blockAct i) (A.blockAct (α.objEquiv i))).card +
        ∑ s : L, (A.compatFailure i s).card +
        ∑ s : L, (RelativeFunctorEstimate.conjFailure E q A
          (RelativeFunctorEstimate.wordBlockAction A ws) i s).card +
        ∑ s : L, (A.wordCompatFailure (π i) (ws s)).card +
        Fintype.card L * ((β.arrow (π i)).sourceDefect +
          k * ((β.arrow (π i)).equivarianceDefect (A.blockAct (π i))
            (A.blockAct (β.objEquiv (π i)))).card) +
        ∑ s : L, (A.wordCompatFailure (β.objEquiv (π i)) (ws s)).card +
        ∑ s : L, (RelativeFunctorEstimate.conjFailure E q⁻¹
          (RelativeFunctorEstimate.wordBlockAction A ws) A (β.objEquiv (π i)) s).card +
        ∑ s : L, (A.compatFailure (α.objEquiv i) s).card := by
    intro i
    unfold stepNineBudget
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hsum : ∑ i ∈ good, E.stepNineBudget α β q A ws k π i =
      ∑ i ∈ good, Fintype.card L * (E.bridge q⁻¹ (π i) i).targetDefect +
        ∑ i ∈ good, Fintype.card L *
          (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)).sourceDefect +
        ∑ i ∈ good, ((α.arrow i).equivarianceDefect (A.blockAct i)
          (A.blockAct (α.objEquiv i))).card +
        ∑ i ∈ good, ∑ s : L, (A.compatFailure i s).card +
        ∑ i ∈ good, ∑ s : L, (RelativeFunctorEstimate.conjFailure E q A
          (RelativeFunctorEstimate.wordBlockAction A ws) i s).card +
        ∑ i ∈ good, ∑ s : L, (A.wordCompatFailure (π i) (ws s)).card +
        ∑ i ∈ good, Fintype.card L * ((β.arrow (π i)).sourceDefect +
          k * ((β.arrow (π i)).equivarianceDefect (A.blockAct (π i))
            (A.blockAct (β.objEquiv (π i)))).card) +
        ∑ i ∈ good, ∑ s : L, (A.wordCompatFailure (β.objEquiv (π i)) (ws s)).card +
        ∑ i ∈ good, ∑ s : L, (RelativeFunctorEstimate.conjFailure E q⁻¹
          (RelativeFunctorEstimate.wordBlockAction A ws) A (β.objEquiv (π i)) s).card +
        ∑ i ∈ good, ∑ s : L, (A.compatFailure (α.objEquiv i) s).card := by
    simp only [hpoint, Finset.sum_add_distrib]
  have hid : ∀ f : I → L → ℕ, ∑ i ∈ good, ∑ s : L, f i s ≤ ∑ s : L, ∑ C, f C s := by
    intro f
    calc ∑ i ∈ good, ∑ s : L, f i s = ∑ s : L, ∑ i ∈ good, f i s := Finset.sum_comm
      _ ≤ ∑ s : L, ∑ C, f C s :=
        Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum_of_subset (Finset.subset_univ good)
  have hre : ∀ g : I → I, Set.InjOn g good → ∀ f : I → L → ℕ,
      ∑ i ∈ good, ∑ s : L, f (g i) s ≤ ∑ s : L, ∑ C, f C s := by
    intro g hg f
    calc ∑ i ∈ good, ∑ s : L, f (g i) s
        = ∑ s : L, ∑ i ∈ good, f (g i) s := Finset.sum_comm
      _ ≤ ∑ s : L, ∑ C, f C s :=
        Finset.sum_le_sum fun s _ ↦ sum_comp_le_sum_univ (fun C ↦ f C s) g good hg
  have hβπ : Set.InjOn (fun i ↦ β.objEquiv (π i)) good := by
    intro a ha b hb h
    exact hπ ha hb (β.objEquiv.injective h)
  have hα : Set.InjOn (fun i ↦ α.objEquiv i) good := by
    intro a _ b _ h
    exact α.objEquiv.injective h
  have h₁ : ∑ i ∈ good, ((α.arrow i).equivarianceDefect (A.blockAct i)
        (A.blockAct (α.objEquiv i))).card ≤
      ∑ i, ((α.arrow i).equivarianceDefect (A.blockAct i)
        (A.blockAct (α.objEquiv i))).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ good)
  have h₂ : ∑ i ∈ good, ∑ s : L, (A.compatFailure i s).card ≤
      ∑ s : L, ∑ C, (A.compatFailure C s).card :=
    hid fun C s ↦ (A.compatFailure C s).card
  have h₃ : ∑ i ∈ good, ∑ s : L, (RelativeFunctorEstimate.conjFailure E q A
        (RelativeFunctorEstimate.wordBlockAction A ws) i s).card ≤
      ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q A
        (RelativeFunctorEstimate.wordBlockAction A ws) C s).card :=
    hid fun C s ↦ (RelativeFunctorEstimate.conjFailure E q A
      (RelativeFunctorEstimate.wordBlockAction A ws) C s).card
  have h₄ : ∑ i ∈ good, ∑ s : L, (A.wordCompatFailure (π i) (ws s)).card ≤
      ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card :=
    hre π hπ fun C s ↦ (A.wordCompatFailure C (ws s)).card
  have h₅ : ∑ i ∈ good, Fintype.card L * ((β.arrow (π i)).sourceDefect +
        k * ((β.arrow (π i)).equivarianceDefect (A.blockAct (π i))
          (A.blockAct (β.objEquiv (π i)))).card) ≤
      ∑ C, Fintype.card L * ((β.arrow C).sourceDefect +
        k * ((β.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (β.objEquiv C))).card) :=
    sum_comp_le_sum_univ (fun C ↦ Fintype.card L * ((β.arrow C).sourceDefect +
      k * ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card)) π good hπ
  have h₆ : ∑ i ∈ good, ∑ s : L, (A.wordCompatFailure (β.objEquiv (π i)) (ws s)).card ≤
      ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card :=
    hre (fun i ↦ β.objEquiv (π i)) hβπ fun C s ↦ (A.wordCompatFailure C (ws s)).card
  have h₇ : ∑ i ∈ good, ∑ s : L, (RelativeFunctorEstimate.conjFailure E q⁻¹
        (RelativeFunctorEstimate.wordBlockAction A ws) A (β.objEquiv (π i)) s).card ≤
      ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q⁻¹
        (RelativeFunctorEstimate.wordBlockAction A ws) A C s).card :=
    hre (fun i ↦ β.objEquiv (π i)) hβπ fun C s ↦ (RelativeFunctorEstimate.conjFailure E q⁻¹
      (RelativeFunctorEstimate.wordBlockAction A ws) A C s).card
  have h₈ : ∑ i ∈ good, ∑ s : L, (A.compatFailure (α.objEquiv i) s).card ≤
      ∑ s : L, ∑ C, (A.compatFailure C s).card :=
    hre (fun i ↦ α.objEquiv i) hα fun C s ↦ (A.compatFailure C s).card
  omega

end BlockEmbedding

end BlockPatching
end GroupApproximation
