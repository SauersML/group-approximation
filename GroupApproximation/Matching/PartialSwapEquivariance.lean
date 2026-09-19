import GroupApproximation.Matching.PartialBijectionExtraction
import GroupApproximation.Matching.PartialClusterCandidates
import GroupApproximation.Sofic.AlmostAutomorphism

/-!
# Equivariance of the swap encoding

The commutation defects of the involution encoding of a partial bijection
inject into the forward and backward partial-equivariance defects.  Missing
points which stay inside the missing set do not create a swap commutator;
this is why the comparison is an inequality rather than an equality.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {Y Z : FiniteModel}

/-- The componentwise label action on the disjoint union. -/
def sumAction (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (s : L) : Equiv.Perm (sumModel Y Z) :=
  Equiv.sumCongr (actY s) (actZ s)

/-- Labelled commutation failures of an arbitrary permutation of the
disjoint union. -/
noncomputable def sumCommutationDefect
    (p : Equiv.Perm (sumModel Y Z))
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    Finset (L × (Y ⊕ Z)) := by
  classical
  exact Finset.univ.filter fun x ↦
    p (sumAction actY actZ x.1 x.2) ≠
      sumAction actY actZ x.1 (p x.2)

omit [DecidableEq L] in
@[simp] theorem mem_sumCommutationDefect
    (p : Equiv.Perm (sumModel Y Z))
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (x : L × (Y ⊕ Z)) :
    x ∈ sumCommutationDefect p actY actZ ↔
      p (sumAction actY actZ x.1 x.2) ≠
        sumAction actY actZ x.1 (p x.2) := by
  classical
  simp [sumCommutationDefect]

omit [DecidableEq L] in
/-- Keeping labels distinct costs at most one factor of `|L|` compared with
the untagged bad-arc set for the finite image of the label maps.  This is the
finite counting interface needed when the label maps are merely permutations,
not homomorphisms coming from an exact group action. -/
theorem card_sumCommutationDefect_le_card_mul_badArcs
    (p : Equiv.Perm (sumModel Y Z))
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    (sumCommutationDefect p actY actZ).card ≤
      Fintype.card L *
        (AlmostAutomorphism.badArcs (sumModel Y Z)
          (Finset.univ.image (sumAction actY actZ)) p).card := by
  classical
  let charge :
      {d // d ∈ sumCommutationDefect p actY actZ} →
        L × {a // a ∈ AlmostAutomorphism.badArcs (sumModel Y Z)
          (Finset.univ.image (sumAction actY actZ)) p} := fun d ↦ by
    refine ⟨d.1.1, ⟨(sumAction actY actZ d.1.1, d.1.2), ?_⟩⟩
    rw [AlmostAutomorphism.mem_badArcs]
    refine ⟨Finset.mem_image.mpr ⟨d.1.1, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (mem_sumCommutationDefect p actY actZ d.1).mp d.2
  have hcharge : Function.Injective charge := by
    intro d e hde
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1) hde
    · exact congrArg (fun x ↦ x.2.1.2) hde
  have hcard := Fintype.card_le_of_injective charge hcharge
  simpa only [Fintype.card_coe, Fintype.card_prod] using hcard

omit [DecidableEq L] in
/-- A left-layer swap commutator is a forward partial-equivariance defect. -/
theorem left_mem_equivarianceDefect_of_swap
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (s : L) (y : Y)
    (h : (s, Sum.inl y) ∈ sumCommutationDefect b.swapPerm actY actZ) :
    (s, y) ∈ b.equivarianceDefect actY actZ := by
  classical
  rw [mem_sumCommutationDefect] at h
  rw [mem_equivarianceDefect]
  intro hy hsy heq
  simp only [sumAction] at h
  rw [swapPerm_inl_of_mem b y hy] at h
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] at h
  rw [swapPerm_inl_of_mem b (actY s y) hsy] at h
  exact h (congrArg Sum.inr heq)

omit [DecidableEq L] in
/-- A right-layer swap commutator is a backward partial-equivariance defect. -/
theorem right_mem_equivarianceDefect_of_swap
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (s : L) (z : Z)
    (h : (s, Sum.inr z) ∈ sumCommutationDefect b.swapPerm actY actZ) :
    (s, z) ∈ b.symm.equivarianceDefect actZ actY := by
  classical
  rw [mem_sumCommutationDefect] at h
  rw [mem_equivarianceDefect]
  intro hz hsz heq
  simp only [sumAction] at h
  rw [swapPerm_inr_of_mem b z hz] at h
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] at h
  rw [swapPerm_inr_of_mem b (actZ s z) hsz] at h
  exact h (congrArg Sum.inl heq)

omit [DecidableEq L] in
/-- Every swap commutator is charged injectively to a forward defect on the
left layer or a backward defect on the right layer. -/
theorem card_swapEquivarianceDefect_le
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    (sumCommutationDefect b.swapPerm actY actZ).card ≤
      (b.equivarianceDefect actY actZ).card +
        (b.symm.equivarianceDefect actZ actY).card := by
  classical
  let charge :
      {p // p ∈ sumCommutationDefect b.swapPerm actY actZ} →
        {p // p ∈ b.equivarianceDefect actY actZ} ⊕
          {p // p ∈ b.symm.equivarianceDefect actZ actY}
    | ⟨(s, Sum.inl y), h⟩ =>
        Sum.inl ⟨(s, y), left_mem_equivarianceDefect_of_swap
          b actY actZ s y h⟩
    | ⟨(s, Sum.inr z), h⟩ =>
        Sum.inr ⟨(s, z), right_mem_equivarianceDefect_of_swap
          b actY actZ s z h⟩
  let forget :
      {p // p ∈ b.equivarianceDefect actY actZ} ⊕
          {p // p ∈ b.symm.equivarianceDefect actZ actY} →
        L × (Y ⊕ Z)
    | Sum.inl p => (p.1.1, Sum.inl p.1.2)
    | Sum.inr p => (p.1.1, Sum.inr p.1.2)
  have hforget (p : {p // p ∈ sumCommutationDefect b.swapPerm actY actZ}) :
      forget (charge p) = p.1 := by
    rcases p with ⟨⟨s, y | z⟩, hp⟩ <;> rfl
  have hcharge : Function.Injective charge := by
    intro p q hpq
    apply Subtype.ext
    rw [← hforget p, hpq, hforget q]
  have hcard := Fintype.card_le_of_injective charge hcharge
  simpa only [Fintype.card_coe, Fintype.card_sum] using hcard

omit [DecidableEq L] in
/-- Forward partial-equivariance defects extracted from a permutation are
charged either to a missing endpoint or to an actual commutation failure of
the permutation on the disjoint union. -/
theorem card_extractCrossing_equivarianceDefect_le
    (p : Equiv.Perm (sumModel Y Z))
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    ((extractCrossing p).equivarianceDefect actY actZ).card ≤
      2 * (Fintype.card L * (extractCrossing p).sourceDefect) +
        (sumCommutationDefect p actY actZ).card := by
  classical
  let Missing := L × {y // y ∈ Finset.univ \ (extractCrossing p).source}
  let Bad := {x // x ∈ sumCommutationDefect p actY actZ}
  let charge :
      {x // x ∈ (extractCrossing p).equivarianceDefect actY actZ} →
        Missing ⊕ (Missing ⊕ Bad) := fun x ↦ by
    by_cases hy : x.1.2 ∈ (extractCrossing p).source
    · by_cases hsy : actY x.1.1 x.1.2 ∈ (extractCrossing p).source
      · apply Sum.inr ∘ Sum.inr
        refine ⟨(x.1.1, Sum.inl x.1.2), ?_⟩
        rw [mem_sumCommutationDefect]
        intro heq
        have hySpec := extractCrossing_apply_spec p x.1.2 hy
        have hsySpec := extractCrossing_apply_spec p (actY x.1.1 x.1.2) hsy
        simp only [sumAction, Equiv.sumCongr_apply, Sum.map_inl] at heq
        rw [hySpec, hsySpec] at heq
        have hne := (mem_equivarianceDefect (extractCrossing p) actY actZ x.1).mp
          x.2 hy hsy
        exact hne (Sum.inr.inj heq)
      · apply Sum.inr ∘ Sum.inl
        exact ⟨x.1.1, ⟨actY x.1.1 x.1.2,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsy⟩⟩⟩
    · apply Sum.inl
      exact ⟨x.1.1, ⟨x.1.2,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩⟩
  let forget : Missing ⊕ (Missing ⊕ Bad) → Option (L × Y)
    | Sum.inl x => some (x.1, x.2.1)
    | Sum.inr (Sum.inl x) => some (x.1, (actY x.1)⁻¹ x.2.1)
    | Sum.inr (Sum.inr x) => match x.1.2 with
      | Sum.inl y => some (x.1.1, y)
      | Sum.inr _ => none
  have hforget
      (x : {x // x ∈ (extractCrossing p).equivarianceDefect actY actZ}) :
      forget (charge x) = some x.1 := by
    dsimp only [charge]
    split
    · split
      · rfl
      · simp [forget]
    · rfl
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Option.some.inj (by rw [← hforget x, hxy, hforget y])
  have hcard := Fintype.card_le_of_injective charge hcharge
  have hcompl :
      (Finset.univ \ (extractCrossing p).source).card =
        (extractCrossing p).sourceDefect := by
    rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ (extractCrossing p).source)]
    simp [FinitePartialBijection.sourceDefect]
  dsimp only [Missing, Bad] at hcard
  simp only [Fintype.card_coe, Fintype.card_sum, Fintype.card_prod, hcompl] at hcard
  omega

omit [DecidableEq L] in
/-- Backward partial-equivariance defects are controlled by missing target
endpoints and commutation failures of the inverse permutation. -/
theorem card_extractCrossing_symm_equivarianceDefect_le
    (p : Equiv.Perm (sumModel Y Z))
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    ((extractCrossing p).symm.equivarianceDefect actZ actY).card ≤
      2 * (Fintype.card L * (extractCrossing p).targetDefect) +
        (sumCommutationDefect p⁻¹ actY actZ).card := by
  classical
  let Missing := L × {z // z ∈ Finset.univ \ (extractCrossing p).target}
  let Bad := {x // x ∈ sumCommutationDefect p⁻¹ actY actZ}
  let charge :
      {x // x ∈ (extractCrossing p).symm.equivarianceDefect actZ actY} →
        Missing ⊕ (Missing ⊕ Bad) := fun x ↦ by
    by_cases hz : x.1.2 ∈ (extractCrossing p).symm.source
    · by_cases hsz : actZ x.1.1 x.1.2 ∈ (extractCrossing p).symm.source
      · apply Sum.inr ∘ Sum.inr
        refine ⟨(x.1.1, Sum.inr x.1.2), ?_⟩
        rw [mem_sumCommutationDefect]
        intro heq
        have hzSpec := extractCrossing_inv_apply_spec p x.1.2 hz
        have hszSpec := extractCrossing_inv_apply_spec p (actZ x.1.1 x.1.2) hsz
        simp only [sumAction, Equiv.sumCongr_apply, Sum.map_inr] at heq
        rw [hzSpec, hszSpec] at heq
        have hne := (mem_equivarianceDefect (extractCrossing p).symm
          actZ actY x.1).mp x.2 hz hsz
        exact hne (Sum.inl.inj heq)
      · apply Sum.inr ∘ Sum.inl
        exact ⟨x.1.1, ⟨actZ x.1.1 x.1.2,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsz⟩⟩⟩
    · apply Sum.inl
      exact ⟨x.1.1, ⟨x.1.2,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩⟩⟩
  let forget : Missing ⊕ (Missing ⊕ Bad) → Option (L × Z)
    | Sum.inl x => some (x.1, x.2.1)
    | Sum.inr (Sum.inl x) => some (x.1, (actZ x.1)⁻¹ x.2.1)
    | Sum.inr (Sum.inr x) => match x.1.2 with
      | Sum.inl _ => none
      | Sum.inr z => some (x.1.1, z)
  have hforget
      (x : {x // x ∈ (extractCrossing p).symm.equivarianceDefect actZ actY}) :
      forget (charge x) = some x.1 := by
    dsimp only [charge]
    split
    · split
      · rfl
      · simp [forget]
    · rfl
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Option.some.inj (by rw [← hforget x, hxy, hforget y])
  have hcard := Fintype.card_le_of_injective charge hcharge
  have hcompl :
      (Finset.univ \ (extractCrossing p).target).card =
        (extractCrossing p).targetDefect := by
    rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ (extractCrossing p).target)]
    simp [FinitePartialBijection.targetDefect]
  dsimp only [Missing, Bad] at hcard
  simp only [Fintype.card_coe, Fintype.card_sum, Fintype.card_prod, hcompl] at hcard
  omega

omit [DecidableEq L] in
/-- The explicit numerical interface from a repaired permutation to a
low-defect cluster candidate.  All three candidate fields are discharged by
the preceding cardinal estimates. -/
theorem isClusterCandidate_extractCrossing_of_bounds
    (p : Equiv.Perm (sumModel Y Z))
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    {h : ℝ} {m : ℕ}
    (hself : (extractCrossing p).sourceDefect +
      (extractCrossing p).targetDefect < 2 * m)
    (hforward :
      ((2 * (Fintype.card L * (extractCrossing p).sourceDefect) +
        (sumCommutationDefect p actY actZ).card : ℕ) : ℝ) < h * m / 2)
    (hbackward :
      ((2 * (Fintype.card L * (extractCrossing p).targetDefect) +
        (sumCommutationDefect p⁻¹ actY actZ).card : ℕ) : ℝ) < h * m / 2) :
    (extractCrossing p).IsClusterCandidate actY actZ h m := by
  refine ⟨hself, ?_, ?_⟩
  · have hcard := card_extractCrossing_equivarianceDefect_le p actY actZ
    have hcardReal :
        (((extractCrossing p).equivarianceDefect actY actZ).card : ℝ) ≤
          (2 * (Fintype.card L * (extractCrossing p).sourceDefect) +
            (sumCommutationDefect p actY actZ).card : ℕ) := by
      exact_mod_cast hcard
    exact hcardReal.trans_lt hforward
  · have hcard := card_extractCrossing_symm_equivarianceDefect_le p actY actZ
    have hcardReal :
        (((extractCrossing p).symm.equivarianceDefect actZ actY).card : ℝ) ≤
          (2 * (Fintype.card L * (extractCrossing p).targetDefect) +
            (sumCommutationDefect p⁻¹ actY actZ).card : ℕ) := by
      exact_mod_cast hcard
    exact hcardReal.trans_lt hbackward

end FinitePartialBijection
end GroupApproximation
