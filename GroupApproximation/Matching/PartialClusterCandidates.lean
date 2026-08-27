import GroupApproximation.Matching.PartialEquivarianceBoundary

/-!
# Low-defect candidates for finite partial-intertwiner clusters

This module packages exactly the hypotheses consumed by the two-sided
separation theorem.  The class is closed under inversion, contains the full
identity, and any two candidates obey the eight-radius gap.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {Y Z : FiniteModel}

/-- A co-large partial bijection whose forward and inverse equivariance
defects are each below half the expansion mass at scale `m`. -/
structure IsClusterCandidate
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (h : ℝ) (m : ℕ) (f : FinitePartialBijection Y Z) : Prop where
  selfSmall : f.sourceDefect + f.targetDefect < 2 * m
  forwardSmall : ((f.equivarianceDefect actY actZ).card : ℝ) < h * m / 2
  backwardSmall : ((f.symm.equivarianceDefect actZ actY).card : ℝ) < h * m / 2

omit [DecidableEq L] in
/-- With at least one label and expansion constant at most two, the forward
candidate inequality alone forces fewer than `m` missing source points. -/
theorem IsClusterCandidate.sourceDefect_lt_scale
    {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m)
    (hL : Nonempty L) (hh : h ≤ 2) : f.sourceDefect < m := by
  letI : Nonempty L := hL
  have hlabels : 1 ≤ Fintype.card L := Fintype.card_pos
  have hdefectNat : f.sourceDefect ≤
      (f.equivarianceDefect actY actZ).card := by
    calc
      f.sourceDefect = 1 * f.sourceDefect := by omega
      _ ≤ Fintype.card L * f.sourceDefect :=
        Nat.mul_le_mul_right f.sourceDefect hlabels
      _ ≤ (f.equivarianceDefect actY actZ).card :=
        card_mul_sourceDefect_le_card_equivarianceDefect f actY actZ
  have hdefect : (f.sourceDefect : ℝ) ≤
      ((f.equivarianceDefect actY actZ).card : ℝ) := by
    exact_mod_cast hdefectNat
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hsourceReal : (f.sourceDefect : ℝ) < m := by
    nlinarith [hf.forwardSmall]
  exact_mod_cast hsourceReal

omit [DecidableEq L] in
/-- The inverse candidate inequality gives the matching target estimate. -/
theorem IsClusterCandidate.targetDefect_lt_scale
    {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m)
    (hL : Nonempty L) (hh : h ≤ 2) : f.targetDefect < m := by
  letI : Nonempty L := hL
  have hlabels : 1 ≤ Fintype.card L := Fintype.card_pos
  have hdefectNat : f.targetDefect ≤
      (f.symm.equivarianceDefect actZ actY).card := by
    calc
      f.targetDefect = 1 * f.targetDefect := by omega
      _ ≤ Fintype.card L * f.targetDefect :=
        Nat.mul_le_mul_right f.targetDefect hlabels
      _ ≤ (f.symm.equivarianceDefect actZ actY).card :=
        card_mul_targetDefect_le_card_symm_equivarianceDefect f actY actZ
  have hdefect : (f.targetDefect : ℝ) ≤
      ((f.symm.equivarianceDefect actZ actY).card : ℝ) := by
    exact_mod_cast hdefectNat
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have htargetReal : (f.targetDefect : ℝ) < m := by
    nlinarith [hf.backwardSmall]
  exact_mod_cast htargetReal

omit [DecidableEq L] in
theorem IsClusterCandidate.symm
    {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) :
    f.symm.IsClusterCandidate actZ actY h m := by
  refine ⟨?_, hf.backwardSmall, ?_⟩
  · simpa [Nat.add_comm] using hf.selfSmall
  · simpa using hf.forwardSmall

omit [DecidableEq L] in
@[simp] theorem equivarianceDefect_refl
    (act : L → Equiv.Perm Y) :
    (FinitePartialBijection.refl Y).equivarianceDefect act act = ∅ := by
  classical
  ext p
  rw [mem_equivarianceDefect]
  simp only [Finset.notMem_empty, iff_false]
  intro hp
  exact hp (Finset.mem_univ _) (Finset.mem_univ _) (by simp)

@[simp] theorem symm_refl :
    (FinitePartialBijection.refl Y).symm = FinitePartialBijection.refl Y := by
  apply FinitePartialBijection.ext_source rfl
  intro y hy
  rfl

omit [DecidableEq L] in
theorem isClusterCandidate_refl
    (act : L → Equiv.Perm Y) {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : 0 < m) :
    (FinitePartialBijection.refl Y).IsClusterCandidate act act h m := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FinitePartialBijection.sourceDefect,
      FinitePartialBijection.targetDefect, FinitePartialBijection.refl]
    omega
  · simp
    positivity
  · rw [symm_refl, equivarianceDefect_refl]
    simp
    positivity

/-- Candidate separation: the expansion of both endpoint actions turns the
two half-budget defect bounds into the exact gap required by
`FinitePartialClusterData` at radius `2m`. -/
theorem IsClusterCandidate.gap
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    {h : ℝ} {m : ℕ}
    (hexpY : HasTaggedExpansionAtScale actY h m)
    (hexpZ : HasTaggedExpansionAtScale actZ h m)
    (hsizeY : 17 * m ≤ Fintype.card Y)
    (hsizeZ : 17 * m ≤ Fintype.card Z)
    (f g : FinitePartialBijection Y Z)
    (hf : f.IsClusterCandidate actY actZ h m)
    (hg : g.IsClusterCandidate actY actZ h m) :
    f.twoSidedDisagreement g < 2 * m ∨
      8 * (2 * m) ≤ f.twoSidedDisagreement g := by
  apply twoSidedDisagreement_lt_two_mul_or_eight_radius_le
    actY actZ f g m hexpY hexpZ hsizeY hsizeZ
  · rw [Nat.cast_add]
    linarith [hf.forwardSmall, hg.forwardSmall]
  · rw [Nat.cast_add]
    linarith [hf.backwardSmall, hg.backwardSmall]

/-- The finite set of all low-defect candidates between two finite models. -/
noncomputable def clusterCandidates
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (h : ℝ) (m : ℕ) : Finset (FinitePartialBijection Y Z) := by
  classical
  letI : Fintype (FinitePartialBijection Y Z) := Fintype.ofFinite _
  exact Finset.univ.filter fun f ↦ f.IsClusterCandidate actY actZ h m

omit [DecidableEq L] in
@[simp] theorem mem_clusterCandidates
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (h : ℝ) (m : ℕ) (f : FinitePartialBijection Y Z) :
    f ∈ clusterCandidates actY actZ h m ↔
      f.IsClusterCandidate actY actZ h m := by
  classical
  simp [clusterCandidates]

end FinitePartialBijection
end GroupApproximation
