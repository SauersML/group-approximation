import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints
import GroupApproximation.Leavitt.ElementaryNoFiniteQuotients

/-!
# Rank-twelve simplicity: exact reductions

This module records the part of Proposition `prop:simple` that follows from
the existing elementary-root API.  Every nonzero elementary root normally
generates `H = EL₁₂(L_{𝔽₂}(1,2))`.  Consequently a proper normal
subgroup meets every elementary root subgroup trivially.

This is not yet simplicity.  The remaining group-theoretic input is a
**root-detection theorem**: every nontrivial normal subgroup of `H` must contain
a nontrivial elementary root.  The manuscript obtains that implication from
Preusser's normal-subgroup theorem together with pure infiniteness, the
exchange property, and the centre computation for the binary Leavitt algebra.
No formal counterpart of that implication is currently present in the
repository, so no `IsSimpleGroup H` instance is asserted here.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-- At rank twelve, an elementary root is trivial exactly when its coefficient
is zero. -/
theorem elementaryRoot_eq_one_iff (i j : Fin 12) (hij : i ≠ j) (a : R) :
    elementaryRoot i j hij a = 1 ↔ a = 0 := by
  constructor
  · intro hroot
    apply elementaryUnit_injective i j hij
    have hval := congrArg Subtype.val hroot
    simpa [elementaryRoot_val] using hval
  · rintro rfl
    exact elementaryRoot_zero i j hij

/-- Any normal subgroup containing a nonzero elementary root is the whole
rank-twelve group.  This is the strongest existing normal-generation theorem
needed after a root has been detected. -/
theorem normal_eq_top_of_nonzero_elementaryRoot_mem
    (N : Subgroup H) (hN : N.Normal)
    (i j : Fin 12) (hij : i ≠ j) (a : R) (ha : a ≠ 0)
    (hmem : elementaryRoot i j hij a ∈ N) :
    N = ⊤ := by
  letI : N.Normal := hN
  apply top_unique
  rw [← HilbertHotel.normalClosure_elementaryRoot_eq_top
    (n := 12) (by omega) i j hij ha]
  exact Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr hmem)

/-- A root coefficient occurring in a proper normal subgroup must vanish. -/
theorem elementaryRoot_coefficient_eq_zero_of_mem_proper_normal
    (N : Subgroup H) (hN : N.Normal) (hproper : N ≠ ⊤)
    (i j : Fin 12) (hij : i ≠ j) (a : R)
    (hmem : elementaryRoot i j hij a ∈ N) :
    a = 0 := by
  by_contra ha
  exact hproper
    (normal_eq_top_of_nonzero_elementaryRoot_mem N hN i j hij a ha hmem)

/-- Equivalently, every proper normal subgroup has trivial intersection with
each additive elementary root subgroup. -/
theorem properNormal_inf_elementaryRootSubgroup_eq_bot
    (N : Subgroup H) (hN : N.Normal) (hproper : N ≠ ⊤)
    (i j : Fin 12) (hij : i ≠ j) :
    N ⊓ elementaryRootSubgroup i j hij = ⊥ := by
  refine le_bot_iff.mp ?_
  intro g hg
  obtain ⟨hgN, hgRoot⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨a, ha⟩ :=
    (mem_elementaryRootSubgroup_iff i j hij g).mp hgRoot
  have ha0 := elementaryRoot_coefficient_eq_zero_of_mem_proper_normal
    N hN hproper i j hij a (ha.symm ▸ hgN)
  apply Subgroup.mem_bot.mpr
  rw [← ha, ha0, elementaryRoot_zero]

/-- No nontrivial elementary root is central in the rank-twelve group.  This
uses only a third index and the Steinberg commutator relation; it does not need
the unavailable computation of the full centre. -/
theorem elementaryRoot_mem_center_iff
    (i j : Fin 12) (hij : i ≠ j) (a : R) :
    elementaryRoot i j hij a ∈ Subgroup.center H ↔ a = 0 := by
  constructor
  · intro hcenter
    obtain ⟨k, hki, hkj⟩ := exists_third_index
      (by norm_num : 3 ≤ Fintype.card (Fin 12)) i j
    have hik : i ≠ k := Ne.symm hki
    have hjk : j ≠ k := Ne.symm hkj
    have hcomm : Commute (elementaryRoot i j hij a)
        (elementaryRoot j k hjk 1) :=
      (Subgroup.mem_center_iff.mp hcenter
        (elementaryRoot j k hjk 1)).symm
    have hroot : elementaryRoot i k hik (a * 1) = 1 := by
      rw [← elementaryRoot_commutator i j k hij hjk hik]
      exact commutatorElement_eq_one_iff_commute.mpr hcomm
    simpa using (elementaryRoot_eq_one_iff i k hik (a * 1)).mp hroot
  · rintro rfl
    simp

/-- Exact reduction of Proposition `prop:simple` to the missing root-detection
statement.  All work after detection is discharged by
`normal_eq_top_of_nonzero_elementaryRoot_mem`. -/
theorem isSimpleGroup_of_normal_root_detection
    (hdetect : ∀ (N : Subgroup H), N.Normal → N ≠ ⊥ →
      ∃ (i j : Fin 12) (hij : i ≠ j) (a : R),
        a ≠ 0 ∧ elementaryRoot i j hij a ∈ N) :
    IsSimpleGroup H where
  exists_pair_ne := ⟨defect, 1, defect_ne_one⟩
  eq_bot_or_eq_top_of_normal := by
    intro N hN
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · refine Or.inr ?_
      obtain ⟨i, j, hij, a, ha, hmem⟩ := hdetect N hN hbot
      exact normal_eq_top_of_nonzero_elementaryRoot_mem
        N hN i j hij a ha hmem

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
