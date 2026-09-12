import GroupApproximation.Matching.PartialBijectionSwap

/-!
# Extracting a partial bijection from a permutation of a disjoint union

The points which a permutation carries from the left summand to the right
summand form the graph of a genuine partial bijection.  This construction is
the inverse of the swap encoding on swap involutions.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {Y Z : FiniteModel}

/-- Left points which a permutation sends into the right summand. -/
noncomputable def crossingSource (p : Equiv.Perm (sumModel Y Z)) : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦ ∃ z : Z, p (Sum.inl y) = Sum.inr z

/-- Right points reached from the left summand by a permutation. -/
noncomputable def crossingTarget (p : Equiv.Perm (sumModel Y Z)) : Finset Z := by
  classical
  exact Finset.univ.filter fun z ↦ ∃ y : Y, p (Sum.inl y) = Sum.inr z

@[simp] theorem mem_crossingSource (p : Equiv.Perm (sumModel Y Z)) (y : Y) :
    y ∈ crossingSource p ↔ ∃ z : Z, p (Sum.inl y) = Sum.inr z := by
  classical
  simp [crossingSource]

@[simp] theorem mem_crossingTarget (p : Equiv.Perm (sumModel Y Z)) (z : Z) :
    z ∈ crossingTarget p ↔ ∃ y : Y, p (Sum.inl y) = Sum.inr z := by
  classical
  simp [crossingTarget]

/-- The right coordinate reached from a crossing source. -/
noncomputable def crossingValue (p : Equiv.Perm (sumModel Y Z))
    (y : Y) (hy : y ∈ crossingSource p) : Z :=
  Classical.choose ((mem_crossingSource p y).mp hy)

theorem crossingValue_spec (p : Equiv.Perm (sumModel Y Z))
    (y : Y) (hy : y ∈ crossingSource p) :
    p (Sum.inl y) = Sum.inr (crossingValue p y hy) :=
  Classical.choose_spec ((mem_crossingSource p y).mp hy)

/-- The left coordinate whose image is a crossing target. -/
noncomputable def crossingPreimage (p : Equiv.Perm (sumModel Y Z))
    (z : Z) (hz : z ∈ crossingTarget p) : Y :=
  Classical.choose ((mem_crossingTarget p z).mp hz)

theorem crossingPreimage_spec (p : Equiv.Perm (sumModel Y Z))
    (z : Z) (hz : z ∈ crossingTarget p) :
    p (Sum.inl (crossingPreimage p z hz)) = Sum.inr z :=
  Classical.choose_spec ((mem_crossingTarget p z).mp hz)

/-- The partial bijection formed by all left-to-right crossings of `p`. -/
noncomputable def extractCrossing (p : Equiv.Perm (sumModel Y Z)) :
    FinitePartialBijection Y Z where
  source := crossingSource p
  target := crossingTarget p
  equiv :=
    { toFun := fun y ↦
        ⟨crossingValue p y.1 y.2,
          (mem_crossingTarget p _).mpr
            ⟨y.1, crossingValue_spec p y.1 y.2⟩⟩
      invFun := fun z ↦
        ⟨crossingPreimage p z.1 z.2,
          (mem_crossingSource p _).mpr
            ⟨z.1, crossingPreimage_spec p z.1 z.2⟩⟩
      left_inv := by
        intro y
        apply Subtype.ext
        apply Sum.inl_injective
        apply p.injective
        rw [crossingPreimage_spec, crossingValue_spec]
      right_inv := by
        intro z
        apply Subtype.ext
        apply Sum.inr_injective
        rw [← crossingValue_spec, crossingPreimage_spec] }

@[simp] theorem extractCrossing_source (p : Equiv.Perm (sumModel Y Z)) :
    (extractCrossing p).source = crossingSource p := rfl

@[simp] theorem extractCrossing_target (p : Equiv.Perm (sumModel Y Z)) :
    (extractCrossing p).target = crossingTarget p := rfl

theorem extractCrossing_apply_spec (p : Equiv.Perm (sumModel Y Z))
    (y : Y) (hy : y ∈ (extractCrossing p).source) :
    p (Sum.inl y) = Sum.inr ((extractCrossing p).apply y hy) :=
  crossingValue_spec p y hy

/-- The inverse permutation realizes the inverse extracted partial map on
every crossing target. -/
theorem extractCrossing_inv_apply_spec (p : Equiv.Perm (sumModel Y Z))
    (z : Z) (hz : z ∈ (extractCrossing p).symm.source) :
    p⁻¹ (Sum.inr z) =
      Sum.inl ((extractCrossing p).symm.apply z hz) := by
  let y := (extractCrossing p).symm.apply z hz
  have hy : y ∈ (extractCrossing p).source :=
    (extractCrossing p).symm.apply_mem_target z hz
  have hforward := extractCrossing_apply_spec p y hy
  have hvalue := (extractCrossing p).apply_symm_apply z hz
  have hp : p (Sum.inl y) = Sum.inr z := by
    calc
      p (Sum.inl y) = Sum.inr ((extractCrossing p).apply y hy) := hforward
      _ = Sum.inr z := congrArg Sum.inr (by
        simpa only [y, proof_irrel_heq] using hvalue)
  calc
    p⁻¹ (Sum.inr z) = p⁻¹ (p (Sum.inl y)) :=
      congrArg (fun x ↦ p⁻¹ x) hp.symm
    _ = Sum.inl y := p.symm_apply_apply _

theorem mem_extractCrossing_source_of_apply_eq
    (p : Equiv.Perm (sumModel Y Z)) (y : Y) (z : Z)
    (h : p (Sum.inl y) = Sum.inr z) : y ∈ (extractCrossing p).source :=
  (mem_crossingSource p y).mpr ⟨z, h⟩

theorem extractCrossing_apply_eq_of_apply_eq
    (p : Equiv.Perm (sumModel Y Z)) (y : Y) (z : Z)
    (h : p (Sum.inl y) = Sum.inr z) :
    (extractCrossing p).apply y
      (mem_extractCrossing_source_of_apply_eq p y z h) = z := by
  apply Sum.inr_injective
  rw [← h]
  exact (extractCrossing_apply_spec p y _).symm

/-- Extracting the crossing partial bijection from its swap involution
recovers the original partial bijection exactly. -/
@[simp] theorem extractCrossing_swapPerm (b : FinitePartialBijection Y Z) :
    extractCrossing b.swapPerm = b := by
  classical
  have hsource : (extractCrossing b.swapPerm).source = b.source := by
    ext y
    constructor
    · intro hy
      rw [extractCrossing_source, mem_crossingSource] at hy
      obtain ⟨z, hz⟩ := hy
      by_cases hsource : y ∈ b.source
      · exact hsource
      · rw [swapPerm_inl_of_not_mem b y hsource] at hz
        exact (Sum.inl_ne_inr hz).elim
    · intro hy
      rw [extractCrossing_source, mem_crossingSource]
      exact ⟨b.apply y hy, swapPerm_inl_of_mem b y hy⟩
  apply FinitePartialBijection.ext_source hsource
  intro y hy
  let hyb : y ∈ b.source := hsource ▸ hy
  have h := extractCrossing_apply_eq_of_apply_eq b.swapPerm y (b.apply y hyb)
    (swapPerm_inl_of_mem b y hyb)
  simpa only [proof_irrel_heq] using h

/-- The source missing from an extracted crossing map is charged either to
source mass already missing from the original partial bijection or to a
left-layer edit of its swap permutation. -/
theorem sourceDefect_extractCrossing_le
    (b : FinitePartialBijection Y Z) (p : Equiv.Perm (sumModel Y Z)) :
    (extractCrossing p).sourceDefect ≤ b.sourceDefect +
      (hammingDisagreement b.swapPerm p).card := by
  classical
  let charge :
      {y // y ∈ Finset.univ \ (extractCrossing p).source} →
        {y // y ∈ Finset.univ \ b.source} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm p} := fun y ↦ by
    by_cases hyb : y.1 ∈ b.source
    · apply Sum.inr
      refine ⟨Sum.inl y.1, ?_⟩
      rw [mem_hammingDisagreement]
      intro heq
      have hpmap : p (Sum.inl y.1) = Sum.inr (b.apply y.1 hyb) := by
        calc
          p (Sum.inl y.1) = b.swapPerm (Sum.inl y.1) := heq.symm
          _ = Sum.inr (b.apply y.1 hyb) := swapPerm_inl_of_mem b y.1 hyb
      have hcross : y.1 ∈ (extractCrossing p).source :=
        mem_extractCrossing_source_of_apply_eq p y.1 (b.apply y.1 hyb) hpmap
      exact (Finset.mem_sdiff.mp y.2).2 hcross
    · exact Sum.inl ⟨y.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyb⟩⟩
  let forget :
      {y // y ∈ Finset.univ \ b.source} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm p} → Option Y
    | Sum.inl y => some y.1
    | Sum.inr x => match x.1 with
      | Sum.inl y => some y
      | Sum.inr _ => none
  have hforget (y : {y // y ∈ Finset.univ \ (extractCrossing p).source}) :
      forget (charge y) = some y.1 := by
    dsimp only [charge]
    split <;> rfl
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Option.some.inj (by rw [← hforget x, hxy, hforget y])
  have hcard := Fintype.card_le_of_injective charge hcharge
  have hsource :
      (Finset.univ \ (extractCrossing p).source).card =
        (extractCrossing p).sourceDefect := by
    rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ (extractCrossing p).source)]
    simp [FinitePartialBijection.sourceDefect]
  have hbsource : (Finset.univ \ b.source).card = b.sourceDefect := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ b.source)]
    simp [FinitePartialBijection.sourceDefect]
  simpa only [Fintype.card_coe, Fintype.card_sum, hsource, hbsource] using hcard

/-- The target analogue, charged through edits of the inverse swap
permutation on the right layer. -/
theorem targetDefect_extractCrossing_le
    (b : FinitePartialBijection Y Z) (p : Equiv.Perm (sumModel Y Z)) :
    (extractCrossing p).targetDefect ≤ b.targetDefect +
      (hammingDisagreement b.swapPerm⁻¹ p⁻¹).card := by
  classical
  let charge :
      {z // z ∈ Finset.univ \ (extractCrossing p).target} →
        {z // z ∈ Finset.univ \ b.target} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm⁻¹ p⁻¹} := fun z ↦ by
    by_cases hzb : z.1 ∈ b.target
    · apply Sum.inr
      refine ⟨Sum.inr z.1, ?_⟩
      rw [mem_hammingDisagreement]
      intro heq
      let y := b.symm.apply z.1 hzb
      have hpInv : p⁻¹ (Sum.inr z.1) = Sum.inl y := by
        calc
          p⁻¹ (Sum.inr z.1) = b.swapPerm⁻¹ (Sum.inr z.1) := heq.symm
          _ = Sum.inl y := swapPerm_inv_inr_of_mem b z.1 hzb
      have hpmap : p (Sum.inl y) = Sum.inr z.1 := by
        calc
          p (Sum.inl y) = p (p⁻¹ (Sum.inr z.1)) := congrArg p hpInv.symm
          _ = Sum.inr z.1 := p.apply_symm_apply _
      have hcross : z.1 ∈ (extractCrossing p).target := by
        change z.1 ∈ crossingTarget p
        exact (mem_crossingTarget p z.1).mpr ⟨y, hpmap⟩
      exact (Finset.mem_sdiff.mp z.2).2 hcross
    · exact Sum.inl ⟨z.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzb⟩⟩
  let forget :
      {z // z ∈ Finset.univ \ b.target} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm⁻¹ p⁻¹} → Option Z
    | Sum.inl z => some z.1
    | Sum.inr x => match x.1 with
      | Sum.inl _ => none
      | Sum.inr z => some z
  have hforget (z : {z // z ∈ Finset.univ \ (extractCrossing p).target}) :
      forget (charge z) = some z.1 := by
    dsimp only [charge]
    split <;> rfl
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Option.some.inj (by rw [← hforget x, hxy, hforget y])
  have hcard := Fintype.card_le_of_injective charge hcharge
  have htarget :
      (Finset.univ \ (extractCrossing p).target).card =
        (extractCrossing p).targetDefect := by
    rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ (extractCrossing p).target)]
    simp [FinitePartialBijection.targetDefect]
  have hbtarget : (Finset.univ \ b.target).card = b.targetDefect := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ b.target)]
    simp [FinitePartialBijection.targetDefect]
  simpa only [Fintype.card_coe, Fintype.card_sum, htarget, hbtarget] using hcard

/-- On the source side, extracting crossings from a perturbed swap costs at
most the original missing source mass plus the permutation disagreement. -/
theorem card_disagreement_extractCrossing_le
    (b : FinitePartialBijection Y Z) (p : Equiv.Perm (sumModel Y Z)) :
    (b.disagreement (extractCrossing p)).card ≤ b.sourceDefect +
      (hammingDisagreement b.swapPerm p).card := by
  classical
  let charge :
      {y // y ∈ b.disagreement (extractCrossing p)} →
        {y // y ∈ Finset.univ \ b.source} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm p} := fun y ↦ by
    by_cases hyb : y.1 ∈ b.source
    · apply Sum.inr
      refine ⟨Sum.inl y.1, ?_⟩
      rw [mem_hammingDisagreement]
      intro heq
      have hpmap : p (Sum.inl y.1) = Sum.inr (b.apply y.1 hyb) := by
        calc
          p (Sum.inl y.1) = b.swapPerm (Sum.inl y.1) := heq.symm
          _ = Sum.inr (b.apply y.1 hyb) := swapPerm_inl_of_mem b y.1 hyb
      let hyp : y.1 ∈ (extractCrossing p).source :=
        mem_extractCrossing_source_of_apply_eq p y.1 (b.apply y.1 hyb) hpmap
      have happ : (extractCrossing p).apply y.1 hyp = b.apply y.1 hyb :=
        extractCrossing_apply_eq_of_apply_eq p y.1 (b.apply y.1 hyb) hpmap
      have hne := (mem_disagreement b (extractCrossing p) y.1).mp y.2 hyb hyp
      exact hne happ.symm
    · exact Sum.inl ⟨y.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyb⟩⟩
  let forget :
      {y // y ∈ Finset.univ \ b.source} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm p} → Option Y
    | Sum.inl y => some y.1
    | Sum.inr x => match x.1 with
      | Sum.inl y => some y
      | Sum.inr _ => none
  have hforget (y : {y // y ∈ b.disagreement (extractCrossing p)}) :
      forget (charge y) = some y.1 := by
    dsimp only [charge]
    split
    · rfl
    · rfl
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Option.some.inj (by rw [← hforget x, hxy, hforget y])
  have hcard := Fintype.card_le_of_injective charge hcharge
  have hcompl : (Finset.univ \ b.source).card = b.sourceDefect := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ b.source)]
    simp [FinitePartialBijection.sourceDefect]
  simpa only [Fintype.card_coe, Fintype.card_sum, hcompl] using hcard

/-- The analogous target-side estimate is charged to disagreement of the
inverse permutations. -/
theorem card_symm_disagreement_extractCrossing_le
    (b : FinitePartialBijection Y Z) (p : Equiv.Perm (sumModel Y Z)) :
    (b.symm.disagreement (extractCrossing p).symm).card ≤ b.targetDefect +
      (hammingDisagreement b.swapPerm⁻¹ p⁻¹).card := by
  classical
  let charge :
      {z // z ∈ b.symm.disagreement (extractCrossing p).symm} →
        {z // z ∈ Finset.univ \ b.target} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm⁻¹ p⁻¹} := fun z ↦ by
    by_cases hzb : z.1 ∈ b.target
    · apply Sum.inr
      refine ⟨Sum.inr z.1, ?_⟩
      rw [mem_hammingDisagreement]
      intro heq
      let y := b.symm.apply z.1 hzb
      have hpInv : p⁻¹ (Sum.inr z.1) = Sum.inl y := by
        calc
          p⁻¹ (Sum.inr z.1) = b.swapPerm⁻¹ (Sum.inr z.1) := heq.symm
          _ = Sum.inl y := swapPerm_inv_inr_of_mem b z.1 hzb
      have hpmap : p (Sum.inl y) = Sum.inr z.1 := by
        calc
          p (Sum.inl y) = p (p⁻¹ (Sum.inr z.1)) := congrArg p hpInv.symm
          _ = Sum.inr z.1 := p.apply_symm_apply _
      let hy : y ∈ (extractCrossing p).source :=
        mem_extractCrossing_source_of_apply_eq p y z.1 hpmap
      have hforward : (extractCrossing p).apply y hy = z.1 :=
        extractCrossing_apply_eq_of_apply_eq p y z.1 hpmap
      have htarget : z.1 ∈ (extractCrossing p).symm.source :=
        by
          have hm := (extractCrossing p).apply_mem_target y hy
          rw [hforward] at hm
          exact hm
      have hbackward : (extractCrossing p).symm.apply z.1 htarget = y := by
        have hinv := (extractCrossing p).symm_apply_apply y hy
        simpa only [proof_irrel_heq, hforward] using hinv
      have hne := (mem_disagreement b.symm (extractCrossing p).symm z.1).mp
        z.2 hzb htarget
      exact hne (by
        simpa only [y, proof_irrel_heq] using hbackward.symm)
    · exact Sum.inl ⟨z.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzb⟩⟩
  let forget :
      {z // z ∈ Finset.univ \ b.target} ⊕
          {x // x ∈ hammingDisagreement b.swapPerm⁻¹ p⁻¹} → Option Z
    | Sum.inl z => some z.1
    | Sum.inr x => match x.1 with
      | Sum.inl _ => none
      | Sum.inr z => some z
  have hforget (z : {z // z ∈ b.symm.disagreement (extractCrossing p).symm}) :
      forget (charge z) = some z.1 := by
    dsimp only [charge]
    split
    · rfl
    · rfl
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Option.some.inj (by rw [← hforget x, hxy, hforget y])
  have hcard := Fintype.card_le_of_injective charge hcharge
  have hcompl : (Finset.univ \ b.target).card = b.targetDefect := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ b.target)]
    simp [FinitePartialBijection.targetDefect]
  simpa only [Fintype.card_coe, Fintype.card_sum, hcompl] using hcard

/-- Two-sided partial disagreement is controlled by the intrinsic missing
mass of the original arrow and the forward and inverse permutation edits. -/
theorem twoSidedDisagreement_extractCrossing_le
    (b : FinitePartialBijection Y Z) (p : Equiv.Perm (sumModel Y Z)) :
    b.twoSidedDisagreement (extractCrossing p) ≤
      b.sourceDefect + b.targetDefect +
        (hammingDisagreement b.swapPerm p).card +
          (hammingDisagreement b.swapPerm⁻¹ p⁻¹).card := by
  have hs := card_disagreement_extractCrossing_le b p
  have ht := card_symm_disagreement_extractCrossing_le b p
  unfold twoSidedDisagreement
  omega

/-- Inverting both finite permutations preserves the number of disagreement
points; this elementary finite bijection is kept local to the extraction
layer to avoid importing any analytic matrix development. -/
theorem card_hammingDisagreement_inv
    (p q : Equiv.Perm (sumModel Y Z)) :
    (hammingDisagreement p⁻¹ q⁻¹).card =
      (hammingDisagreement p q).card := by
  classical
  refine Finset.card_bij (fun y _ ↦ p⁻¹ y) ?_ ?_ ?_
  · intro y hy
    rw [mem_hammingDisagreement] at hy ⊢
    intro hcon
    apply hy
    have hy' : p (p⁻¹ y) = y := by simp
    rw [hy'] at hcon
    have hstep : q⁻¹ y = p⁻¹ y := by
      conv_lhs => rw [hcon]
      simp
    exact hstep.symm
  · intro a _ b _ hab
    have := congrArg (fun z ↦ p z) hab
    simpa using this
  · intro x hx
    rw [mem_hammingDisagreement] at hx
    refine ⟨p x, ?_, by simp⟩
    rw [mem_hammingDisagreement]
    intro hcon
    apply hx
    have hxx : p⁻¹ (p x) = x := by simp
    rw [hxx] at hcon
    have := congrArg (fun z ↦ q z) hcon
    simpa using this.symm

/-- A single permutation edit budget controls both sides of the extracted
partial arrow. -/
theorem twoSidedDisagreement_extractCrossing_le_self_add_two_mul
    (b : FinitePartialBijection Y Z) (p : Equiv.Perm (sumModel Y Z)) :
    b.twoSidedDisagreement (extractCrossing p) ≤
      b.sourceDefect + b.targetDefect +
        2 * (hammingDisagreement b.swapPerm p).card := by
  have h := twoSidedDisagreement_extractCrossing_le b p
  rw [card_hammingDisagreement_inv b.swapPerm p] at h
  omega

end FinitePartialBijection
end GroupApproximation
