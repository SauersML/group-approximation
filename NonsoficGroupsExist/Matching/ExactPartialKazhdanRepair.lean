import NonsoficGroupsExist.Kazhdan.DiagonalInvariantRelation
import NonsoficGroupsExist.Matching.PartialSwapEquivariance
import NonsoficGroupsExist.Matching.PartialEquivarianceComposition

/-!
# Exact Kazhdan repair for finite partial intertwiners

A partial bijection between two finite `G`-sets is encoded by its swap
involution on their disjoint union.  The two actions combine to an exact
action on that union.  Applying diagonal Kazhdan repair to the swap and then
extracting its left-to-right crossings produces a repaired partial
bijection.  This file gives the explicit two-sided distance estimate needed
by the finite cluster-composition interface.
-/

namespace NonsoficGroupsExist
namespace ExactPartialKazhdanRepair

open DiagonalInvariantRelation
open FinitePartialBijection

universe u

variable {G : Type u} [Group G]
variable {Y Z : FiniteModel}

/-- Componentwise exact action on a disjoint union. -/
def sumActionHom (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z) :
    G →* Equiv.Perm (sumModel Y Z) where
  toFun g := sumAction σY σZ g
  map_one' := by
    ext x
    cases x <;> simp [sumAction]
  map_mul' g h := by
    ext x
    cases x <;> simp [sumAction]

@[simp] theorem sumActionHom_apply
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (g : G) (x : Y ⊕ Z) :
    sumActionHom σY σZ g x = Sum.map (σY g) (σZ g) x := by
  cases x <;> rfl

/-- Repair the swap permutation and extract its crossing partial map. -/
noncomputable def repair
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) : FinitePartialBijection Y Z :=
  extractCrossing
    (roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm)

/-- Repair introduces at most one new missing source for each point where the
rounded permutation differs from the original swap. -/
theorem sourceDefect_repair_le
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    (repair σY σZ b).sourceDefect ≤ b.sourceDefect +
      (hammingDisagreement b.swapPerm
        (roundedDiagonalPermutation
          (sumActionHom σY σZ) b.swapPerm)).card := by
  exact sourceDefect_extractCrossing_le b
    (roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm)

/-- The same edit budget controls new missing targets. -/
theorem targetDefect_repair_le
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    (repair σY σZ b).targetDefect ≤ b.targetDefect +
      (hammingDisagreement b.swapPerm
        (roundedDiagonalPermutation
          (sumActionHom σY σZ) b.swapPerm)).card := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have h := targetDefect_extractCrossing_le b p
  rw [card_hammingDisagreement_inv b.swapPerm p] at h
  exact h

/-- Both missing-endpoint budgets after repair are controlled by the original
missing mass and twice the rounded-permutation edit count. -/
theorem missingMass_repair_le
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    (repair σY σZ b).sourceDefect + (repair σY σZ b).targetDefect ≤
      b.sourceDefect + b.targetDefect +
        2 * (hammingDisagreement b.swapPerm
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)).card := by
  have hs := sourceDefect_repair_le σY σZ b
  have ht := targetDefect_repair_le σY σZ b
  omega

/-- The original forward and backward partial-equivariance defects, summed
with generator labels retained.  `Unit` packages one label at a time so no
collision between equal finite permutations can erase multiplicity. -/
noncomputable def partialTotalDefect
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) : ℕ :=
  ∑ q ∈ Q,
    ((b.equivarianceDefect
        (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)).card +
      (b.symm.equivarianceDefect
        (fun _ : Unit ↦ σZ q) (fun _ : Unit ↦ σY q)).card)

/-- The tagged defect over the subtype `Q` is exactly the sum of the
one-label defects.  This prevents either overcounting or loss of multiplicity
when passing between the candidate and Kazhdan-repair interfaces. -/
theorem card_taggedEquivarianceDefect_eq_sum_singleton
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) :
    (b.equivarianceDefect
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card =
      ∑ q : ↥Q,
        (b.equivarianceDefect
          (fun _ : Unit ↦ σY q.1) (fun _ : Unit ↦ σZ q.1)).card := by
  classical
  let F :
      {d // d ∈ b.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)} →
        Σ q : ↥Q, {d // d ∈ b.equivarianceDefect
          (fun _ : Unit ↦ σY q.1) (fun _ : Unit ↦ σZ q.1)} := fun d ↦ by
    refine ⟨d.1.1, ⟨(Unit.unit, d.1.2), ?_⟩⟩
    have hd := (mem_equivarianceDefect b
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) d.1).mp d.2
    rw [mem_equivarianceDefect]
    exact hd
  have hF : Function.Bijective F := by
    constructor
    · intro d e hde
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun x ↦ x.1) hde
      · exact congrArg (fun x ↦ x.2.1.2) hde
    · rintro ⟨q, ⟨⟨u, y⟩, hy⟩⟩
      cases u
      have htag : (q, y) ∈ b.equivarianceDefect
          (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) := by
        rw [mem_equivarianceDefect] at hy ⊢
        exact hy
      refine ⟨⟨(q, y), htag⟩, ?_⟩
      rfl
  let e := Equiv.ofBijective F hF
  have hcard := Fintype.card_congr e
  rw [Fintype.card_sigma] at hcard
  simpa only [Fintype.card_coe] using hcard

/-- `partialTotalDefect` is precisely the sum of the forward and backward
candidate defect cardinalities with `Q` retained as a subtype. -/
theorem partialTotalDefect_eq_tagged
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) :
    partialTotalDefect σY σZ Q b =
      (b.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card +
      (b.symm.equivarianceDefect
        (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)).card := by
  rw [card_taggedEquivarianceDefect_eq_sum_singleton,
    card_taggedEquivarianceDefect_eq_sum_singleton]
  unfold partialTotalDefect
  rw [Finset.sum_add_distrib]
  rw [← Q.sum_attach, ← Q.sum_attach]
  rw [Finset.attach_eq_univ]

/-- Native total defect is subadditive under composition of partial
intertwiners, with all four forward/backward input contributions explicit. -/
theorem partialTotalDefect_trans_le
    {X : FiniteModel}
    (σX : G →* Equiv.Perm X) (σY : G →* Equiv.Perm Y)
    (σZ : G →* Equiv.Perm Z) (Q : Finset G)
    (f : FinitePartialBijection X Y)
    (g : FinitePartialBijection Y Z) :
    partialTotalDefect σX σZ Q (f.trans g) ≤
      (f.equivarianceDefect
        (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1)).card +
      (g.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card +
      (f.symm.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σX q.1)).card +
      (g.symm.equivarianceDefect
        (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)).card := by
  classical
  rw [partialTotalDefect_eq_tagged]
  have hforward := card_equivarianceDefect_trans_le
    (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1)
    (fun q : ↥Q ↦ σZ q.1) f g
  have hbackward := card_equivarianceDefect_trans_le
    (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)
    (fun q : ↥Q ↦ σX q.1) g.symm f.symm
  rw [f.symm_trans g]
  omega

/-- Candidate bounds turn the preceding four-term estimate into the clean
strict real budget `2 h m`. -/
theorem partialTotalDefect_trans_lt_two_mul
    {X : FiniteModel}
    (σX : G →* Equiv.Perm X) (σY : G →* Equiv.Perm Y)
    (σZ : G →* Equiv.Perm Z) (Q : Finset G)
    (f : FinitePartialBijection X Y)
    (hf : f.IsClusterCandidate
      (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1) h m)
    (g : FinitePartialBijection Y Z)
    (hg : g.IsClusterCandidate
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m) :
    (partialTotalDefect σX σZ Q (f.trans g) : ℝ) < 2 * h * m := by
  have htotalNat := partialTotalDefect_trans_le σX σY σZ Q f g
  have htotal : (partialTotalDefect σX σZ Q (f.trans g) : ℝ) ≤
      ((f.equivarianceDefect
        (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1)).card +
      (g.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card +
      (f.symm.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σX q.1)).card +
      (g.symm.equivarianceDefect
        (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)).card : ℕ) := by
    exact_mod_cast htotalNat
  push_cast at htotal
  nlinarith [hf.forwardSmall, hf.backwardSmall,
    hg.forwardSmall, hg.backwardSmall]

/-- For one label, every bad arc of the swap embeds into the tagged
commutation-defect set used by the partial-equivariance comparison. -/
theorem card_badArcs_singleton_swap_le_sumCommutationDefect
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (q : G) (b : FinitePartialBijection Y Z) :
    (AlmostAutomorphism.badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm).card ≤
      (sumCommutationDefect b.swapPerm
        (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)).card := by
  let F :
      {p // p ∈ AlmostAutomorphism.badArcs (sumModel Y Z)
        {sumAction σY σZ q} b.swapPerm} →
      {p // p ∈ sumCommutationDefect b.swapPerm
        (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)} := fun p ↦ by
    refine ⟨(Unit.unit, p.1.2), ?_⟩
    rw [mem_sumCommutationDefect]
    have hp := (AlmostAutomorphism.mem_badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm p.1).1 p.2
    have hlabel : p.1.1 = sumAction σY σZ q := by simpa using hp.1
    rw [hlabel] at hp
    change b.swapPerm (sumAction σY σZ q p.1.2) ≠
      sumAction σY σZ q (b.swapPerm p.1.2)
    exact hp.2
  have hF : Function.Injective F := by
    intro p r hpr
    apply Subtype.ext
    have hvertex : p.1.2 = r.1.2 :=
      congrArg (fun x ↦ x.1.2) hpr
    have hp := (AlmostAutomorphism.mem_badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm p.1).1 p.2
    have hr := (AlmostAutomorphism.mem_badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm r.1).1 r.2
    have hpLabel : p.1.1 = sumAction σY σZ q := by simpa using hp.1
    have hrLabel : r.1.1 = sumAction σY σZ q := by simpa using hr.1
    exact Prod.ext (hpLabel.trans hrLabel.symm) hvertex
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hF

/-- The swap commutation defect is bounded by the sum of the original
forward and backward partial-equivariance defects. -/
theorem totalCommutationDefect_swap_le_partialTotalDefect
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) :
    totalCommutationDefect (sumActionHom σY σZ) Q b.swapPerm ≤
      partialTotalDefect σY σZ Q b := by
  rw [totalCommutationDefect, partialTotalDefect]
  apply Finset.sum_le_sum
  intro q _
  refine (card_badArcs_singleton_swap_le_sumCommutationDefect
    σY σZ q b).trans ?_
  exact card_swapEquivarianceDefect_le b
    (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)

/-- Retaining every element of `Q` as a distinct label costs at most a
factor `|Q|` relative to the bad-arc set indexed by the finite image of the
action.  The explicit first coordinate makes the charge injective even when
two group elements induce the same finite permutation. -/
theorem card_taggedSumCommutationDefect_le_card_mul_badArcs
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (p : Equiv.Perm (sumModel Y Z)) :
    (sumCommutationDefect p
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card ≤
      Q.card *
        (AlmostAutomorphism.badArcs (sumModel Y Z)
          (Q.image (sumActionHom σY σZ)) p).card := by
  classical
  let charge :
      {d // d ∈ sumCommutationDefect p
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)} →
        ↥Q × {a // a ∈ AlmostAutomorphism.badArcs (sumModel Y Z)
          (Q.image (sumActionHom σY σZ)) p} := fun d ↦ by
    refine ⟨d.1.1, ⟨(sumAction σY σZ d.1.1.1, d.1.2), ?_⟩⟩
    rw [AlmostAutomorphism.mem_badArcs]
    refine ⟨Finset.mem_image.mpr ⟨d.1.1.1, d.1.1.2, ?_⟩, ?_⟩
    · rfl
    · exact (mem_sumCommutationDefect p
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) d.1).mp d.2
  have hcharge : Function.Injective charge := by
    intro d e hde
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1) hde
    · exact congrArg (fun x ↦ x.2.1.2) hde
  have hcard := Fintype.card_le_of_injective charge hcharge
  simpa only [Fintype.card_coe, Fintype.card_prod] using hcard

/-- The repaired arrow is close to the original partial arrow.  The intrinsic
missing source and target masses are retained explicitly; every additional
disagreement is controlled by the Kazhdan repair of the swap permutation. -/
theorem kazhdan_mul_twoSidedDisagreement_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * (b.twoSidedDisagreement (repair σY σZ b) : ℝ) ≤
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
        16 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htwoNat :=
    twoSidedDisagreement_extractCrossing_le_self_add_two_mul b p
  have htwo : (b.twoSidedDisagreement (extractCrossing p) : ℝ) ≤
      (b.sourceDefect + b.targetDefect : ℕ) +
        2 * ((hammingDisagreement b.swapPerm p).card : ℕ) := by
    exact_mod_cast htwoNat
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left htwo (sq_nonneg ε)
  change ε ^ 2 * (b.twoSidedDisagreement (extractCrossing p) : ℝ) ≤ _
  nlinarith

/-- Quantitative preservation of co-large source and target sets under the
same exact Kazhdan repair. -/
theorem kazhdan_mul_missingMass_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) ≤
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
        16 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have hmissingNat := missingMass_repair_le σY σZ b
  have hmissing :
      ((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) ≤
        (b.sourceDefect + b.targetDefect : ℕ) +
          2 * ((hammingDisagreement b.swapPerm p).card : ℕ) := by
    simpa only [p] using hmissingNat
  have hmissingReal :
      (((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) : ℝ) ≤
        (b.sourceDefect + b.targetDefect : ℕ) +
          2 * ((hammingDisagreement b.swapPerm p).card : ℕ) := by
    exact_mod_cast hmissing
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left hmissingReal (sq_nonneg ε)
  nlinarith

/-- Source-side form of the missing-mass estimate. -/
theorem kazhdan_mul_sourceDefect_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * ((repair σY σZ b).sourceDefect : ℝ) ≤
      ε ^ 2 * (b.sourceDefect : ℝ) +
        8 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have hsNat := sourceDefect_repair_le σY σZ b
  have hs : ((repair σY σZ b).sourceDefect : ℝ) ≤
      (b.sourceDefect : ℝ) +
        ((hammingDisagreement b.swapPerm p).card : ℝ) := by
    exact_mod_cast hsNat
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left hs (sq_nonneg ε)
  nlinarith

/-- Target-side form of the missing-mass estimate. -/
theorem kazhdan_mul_targetDefect_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * ((repair σY σZ b).targetDefect : ℝ) ≤
      ε ^ 2 * (b.targetDefect : ℝ) +
        8 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htNat := targetDefect_repair_le σY σZ b
  have ht : ((repair σY σZ b).targetDefect : ℝ) ≤
      (b.targetDefect : ℝ) +
        ((hammingDisagreement b.swapPerm p).card : ℝ) := by
    exact_mod_cast htNat
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left ht (sq_nonneg ε)
  nlinarith

/-- The same distance estimate expressed entirely in the native forward and
backward partial-equivariance defects of the input arrow. -/
theorem kazhdan_mul_twoSidedDisagreement_repair_le_partialDefect
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * (b.twoSidedDisagreement (repair σY σZ b) : ℝ) ≤
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
        16 * (partialTotalDefect σY σZ Q b : ℝ) := by
  have hrepair := kazhdan_mul_twoSidedDisagreement_repair_le hQ σY σZ b
  have hdefectNat :=
    totalCommutationDefect_swap_le_partialTotalDefect σY σZ Q b
  have hdefect :
      (totalCommutationDefect (sumActionHom σY σZ) Q b.swapPerm : ℝ) ≤
        partialTotalDefect σY σZ Q b := by
    exact_mod_cast hdefectNat
  linarith

/-- The repaired swap itself has quantitatively controlled commutation
defect for the finite image of `Q`. -/
theorem kazhdan_mul_card_badArcs_repairedSwap_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((AlmostAutomorphism.badArcs (sumModel Y Z)
          (Q.image (sumActionHom σY σZ))
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)).card : ℝ) ≤
      8 * (Q.card : ℝ) *
        (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) :=
  kazhdan_mul_card_badArcs_roundedDiagonalPermutation_le
    hQ (sumActionHom σY σZ) b.swapPerm

/-- Forward `Q`-tagged commutation defects of the repaired swap, with no
loss of labels that happen to act by the same finite permutation. -/
theorem kazhdan_mul_card_taggedSumCommutationDefect_repaired_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((sumCommutationDefect
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)
          (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
      8 * (Q.card : ℝ) ^ 2 *
        (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htagNat :=
    card_taggedSumCommutationDefect_le_card_mul_badArcs σY σZ Q p
  have htag :
      ((sumCommutationDefect p
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
        (Q.card : ℝ) *
          (AlmostAutomorphism.badArcs (sumModel Y Z)
            (Q.image (sumActionHom σY σZ)) p).card := by
    exact_mod_cast htagNat
  have hbad := kazhdan_mul_card_badArcs_repairedSwap_le hQ σY σZ b
  have hscaled := mul_le_mul_of_nonneg_left htag (sq_nonneg ε)
  have hQ0 : 0 ≤ (Q.card : ℝ) := by positivity
  nlinarith

/-- The inverse repaired permutation has the same bad-arc cardinality, so
the identical quantitative bound controls backward tagged defects. -/
theorem kazhdan_mul_card_taggedSumCommutationDefect_repaired_inv_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((sumCommutationDefect
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)⁻¹
          (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
      8 * (Q.card : ℝ) ^ 2 *
        (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htagNat :=
    card_taggedSumCommutationDefect_le_card_mul_badArcs σY σZ Q p⁻¹
  have htag :
      ((sumCommutationDefect p⁻¹
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
        (Q.card : ℝ) *
          (AlmostAutomorphism.badArcs (sumModel Y Z)
            (Q.image (sumActionHom σY σZ)) p⁻¹).card := by
    exact_mod_cast htagNat
  have hbad := kazhdan_mul_card_badArcs_repairedSwap_le hQ σY σZ b
  rw [AlmostAutomorphism.card_badArcs_inv] at htag
  have hscaled := mul_le_mul_of_nonneg_left htag (sq_nonneg ε)
  have hQ0 : 0 ≤ (Q.card : ℝ) := by positivity
  nlinarith

/-- Complete numerical interface from exact Kazhdan repair to the finite
cluster machinery.  The three strict hypotheses are stated entirely in
terms of the input partial arrow and its original labelled commutation
defect.  They imply simultaneously that the repaired crossing is a
low-defect candidate and that it lies inside the required radius. -/
theorem repair_isClusterCandidate_and_close_of_bounds
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) {h : ℝ} {m : ℕ}
    (hclose :
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
          16 * (totalCommutationDefect
            (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * ((2 * m : ℕ) : ℝ))
    (hforward :
      2 * (Q.card : ℝ) *
          (ε ^ 2 * (b.sourceDefect : ℝ) +
            8 * (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * (h * m / 2))
    (hbackward :
      2 * (Q.card : ℝ) *
          (ε ^ 2 * (b.targetDefect : ℝ) +
            8 * (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * (h * m / 2)) :
    (repair σY σZ b).IsClusterCandidate
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m ∧
      (repair σY σZ b).twoSidedDisagreement b < 2 * m := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hmissing := kazhdan_mul_missingMass_repair_le hQ σY σZ b
  have hselfScaled := hmissing.trans_lt hclose
  have hselfReal :
      (((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) : ℝ) <
        ((2 * m : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_left hselfScaled hεsq.le
  have hself :
      (repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect < 2 * m := by
    exact_mod_cast hselfReal
  have hs := kazhdan_mul_sourceDefect_repair_le hQ σY σZ b
  have hfTag :=
    kazhdan_mul_card_taggedSumCommutationDefect_repaired_le hQ σY σZ b
  have hsMul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * (Q.card : ℝ) by positivity)
  have hfCombined :
      ε ^ 2 *
          ((2 * (Fintype.card ↥Q * (repair σY σZ b).sourceDefect) +
            (sumCommutationDefect p
              (fun q : ↥Q ↦ σY q.1)
              (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) ≤
        2 * (Q.card : ℝ) *
            (ε ^ 2 * (b.sourceDefect : ℝ) +
              8 * (totalCommutationDefect
                (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
    simp only [Fintype.card_coe]
    push_cast
    dsimp only [p] at hfTag ⊢
    nlinarith
  have hfScaled := hfCombined.trans_lt hforward
  have hfReal :
      ((2 * (Fintype.card ↥Q * (repair σY σZ b).sourceDefect) +
        (sumCommutationDefect p
          (fun q : ↥Q ↦ σY q.1)
          (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) < h * m / 2 :=
    lt_of_mul_lt_mul_left hfScaled hεsq.le
  have ht := kazhdan_mul_targetDefect_repair_le hQ σY σZ b
  have hbTag :=
    kazhdan_mul_card_taggedSumCommutationDefect_repaired_inv_le
      hQ σY σZ b
  have htMul := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ 2 * (Q.card : ℝ) by positivity)
  have hbCombined :
      ε ^ 2 *
          ((2 * (Fintype.card ↥Q * (repair σY σZ b).targetDefect) +
            (sumCommutationDefect p⁻¹
              (fun q : ↥Q ↦ σY q.1)
              (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) ≤
        2 * (Q.card : ℝ) *
            (ε ^ 2 * (b.targetDefect : ℝ) +
              8 * (totalCommutationDefect
                (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
    simp only [Fintype.card_coe]
    push_cast
    dsimp only [p] at hbTag ⊢
    nlinarith
  have hbScaled := hbCombined.trans_lt hbackward
  have hbReal :
      ((2 * (Fintype.card ↥Q * (repair σY σZ b).targetDefect) +
        (sumCommutationDefect p⁻¹
          (fun q : ↥Q ↦ σY q.1)
          (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) < h * m / 2 :=
    lt_of_mul_lt_mul_left hbScaled hεsq.le
  have hcand :
      (extractCrossing p).IsClusterCandidate
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m :=
    isClusterCandidate_extractCrossing_of_bounds p
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)
      (by simpa only [repair, p] using hself)
      (by simpa only [repair, p] using hfReal)
      (by simpa only [repair, p] using hbReal)
  have hdist := kazhdan_mul_twoSidedDisagreement_repair_le hQ σY σZ b
  have hdistScaled := hdist.trans_lt hclose
  have hdistReal :
      (b.twoSidedDisagreement (repair σY σZ b) : ℝ) <
        ((2 * m : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_left hdistScaled hεsq.le
  have hdistNat : b.twoSidedDisagreement (repair σY σZ b) < 2 * m := by
    exact_mod_cast hdistReal
  refine ⟨?_, ?_⟩
  · simpa only [repair, p] using hcand
  · rw [twoSidedDisagreement_comm]
    exact hdistNat

end ExactPartialKazhdanRepair
end NonsoficGroupsExist
