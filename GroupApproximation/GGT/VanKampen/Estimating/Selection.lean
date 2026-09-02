import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

/-!
# Finite maximal contiguity selection

This file proves the finite maximization in Osin's Appendix Definition `M`.
For a finite type of candidate contiguity regions and a disjointness relation,
an admissible family is pairwise disjoint.  A distinguished family first
maximizes the total contiguity-arc length and then minimizes its cardinality
among all maximizers.

The construction uses the powerset of the finite candidate set, so both
optimizations are explicit finite selections.  The diagram-specific layer
only has to provide a finite candidate type, its arc-length weight, and the
geometric disjointness relation.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u

namespace EstimatingSelection

/-- A family of candidates is pairwise compatible when every two distinct
members satisfy the supplied disjointness relation. -/
def PairwiseCompatible {C : Type u} (compatible : C → C → Prop)
    (family : Finset C) : Prop :=
  ∀ a ∈ family, ∀ b ∈ family, a ≠ b → compatible a b

/-- The total contiguity-arc length of a finite candidate family. -/
def familyWeight {C : Type u} (weight : C → ℕ) (family : Finset C) : ℕ :=
  ∑ candidate ∈ family, weight candidate

/-- All pairwise-compatible families of a finite candidate type. -/
noncomputable def admissibleFamilies {C : Type u} [Fintype C]
    (compatible : C → C → Prop) : Finset (Finset C) := by
  classical
  exact Finset.univ.powerset.filter fun family =>
    PairwiseCompatible compatible family

/-- Membership in `admissibleFamilies` is exactly pairwise compatibility. -/
theorem mem_admissibleFamilies_iff {C : Type u} [Fintype C]
    (compatible : C → C → Prop) (family : Finset C) :
    family ∈ admissibleFamilies compatible ↔
      PairwiseCompatible compatible family := by
  classical
  simp only [admissibleFamilies, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]

/-- The empty family is admissible, so the finite optimization domain is
nonempty even when there are no candidate regions. -/
theorem admissibleFamilies_nonempty {C : Type u} [Fintype C]
    (compatible : C → C → Prop) :
    (admissibleFamilies compatible).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  rw [mem_admissibleFamilies_iff]
  intro a ha
  simp at ha

/-- Osin's distinguished family: pairwise disjoint, maximal for total
contiguity-arc length, and of minimal cardinality among all maximizers. -/
structure DistinguishedFamily {C : Type u} [Fintype C]
    (compatible : C → C → Prop) (weight : C → ℕ) where
  family : Finset C
  pairwise : PairwiseCompatible compatible family
  weight_maximal : ∀ other : Finset C,
    PairwiseCompatible compatible other →
      familyWeight weight other ≤ familyWeight weight family
  card_minimal : ∀ other : Finset C,
    PairwiseCompatible compatible other →
      familyWeight weight other = familyWeight weight family →
        family.card ≤ other.card

/-- The maximizers of the total contiguity-arc length. -/
noncomputable def weightMaximizers {C : Type u} [Fintype C]
    (compatible : C → C → Prop) (weight : C → ℕ)
    (maxWeight : ℕ) : Finset (Finset C) := by
  classical
  exact (admissibleFamilies compatible).filter fun family =>
    familyWeight weight family = maxWeight

/-- A chosen maximum belongs to the finite set of maximizers. -/
theorem chosen_mem_weightMaximizers {C : Type u} [Fintype C]
    (compatible : C → C → Prop) (weight : C → ℕ)
    (chosen : Finset C) (hchosen : chosen ∈ admissibleFamilies compatible) :
    chosen ∈ weightMaximizers compatible weight (familyWeight weight chosen) := by
  classical
  simp only [weightMaximizers, Finset.mem_filter, hchosen, true_and]

/-- Explicit finite maximization produces a distinguished family.  The first
selection maximizes total arc length; the second minimizes cardinality inside
the finite set of maximizers. -/
theorem exists_distinguishedFamily {C : Type u} [Fintype C]
    (compatible : C → C → Prop) (weight : C → ℕ) :
    Nonempty (DistinguishedFamily compatible weight) := by
  classical
  obtain ⟨maximumFamily, hmaximumAdmissible, hmaximum⟩ :=
    Finset.exists_max_image (admissibleFamilies compatible)
      (familyWeight weight) (admissibleFamilies_nonempty compatible)
  let maximizers := weightMaximizers compatible weight
    (familyWeight weight maximumFamily)
  have hmaximizersNonempty : maximizers.Nonempty := by
    refine ⟨maximumFamily, ?_⟩
    exact chosen_mem_weightMaximizers compatible weight maximumFamily
      hmaximumAdmissible
  obtain ⟨minimumFamily, hminimumMaximizer, hminimum⟩ :=
    Finset.exists_min_image maximizers Finset.card hmaximizersNonempty
  have hminimumData :
      minimumFamily ∈ admissibleFamilies compatible ∧
        familyWeight weight minimumFamily =
          familyWeight weight maximumFamily := by
    simpa only [maximizers, weightMaximizers, Finset.mem_filter] using
      hminimumMaximizer
  refine ⟨{
    family := minimumFamily
    pairwise := (mem_admissibleFamilies_iff compatible minimumFamily).mp
      hminimumData.1
    weight_maximal := ?_
    card_minimal := ?_ }⟩
  · intro other hother
    have hotherAdmissible : other ∈ admissibleFamilies compatible :=
      (mem_admissibleFamilies_iff compatible other).mpr hother
    rw [hminimumData.2]
    exact hmaximum other hotherAdmissible
  · intro other hother hweight
    have hotherAdmissible : other ∈ admissibleFamilies compatible :=
      (mem_admissibleFamilies_iff compatible other).mpr hother
    have hotherMaximum : familyWeight weight other =
        familyWeight weight maximumFamily := hweight.trans hminimumData.2
    have hotherMem : other ∈ maximizers := by
      simp only [maximizers, weightMaximizers, Finset.mem_filter,
        hotherAdmissible, hotherMaximum, and_self]
    exact hminimum other hotherMem

/-! ## Replacement consequences of Definition M -/

/-- No compatible replacement can have both at least the selected total
arc length and fewer members.  A larger weight contradicts the first
optimization in Definition `M`; equal weight and smaller cardinality
contradict its second optimization.  This is the finite-selection
contradiction used when Osin merges parallel edges or an empty two-gon. -/
theorem not_weight_ge_and_card_lt {C : Type u} [Fintype C]
    {compatible : C → C → Prop} {weight : C → ℕ}
    (selected : DistinguishedFamily compatible weight)
    (replacement : Finset C)
    (hreplacement : PairwiseCompatible compatible replacement) :
    ¬ (familyWeight weight selected.family ≤
          familyWeight weight replacement ∧
        replacement.card < selected.family.card) := by
  rintro ⟨hweight, hcard⟩
  have hreverse := selected.weight_maximal replacement hreplacement
  have hequal : familyWeight weight replacement =
      familyWeight weight selected.family := le_antisymm hreverse hweight
  have hminimal := selected.card_minimal replacement hreplacement hequal
  omega

/-- Consequently, a compatible replacement with no smaller total length has
at least as many regions as the distinguished family. -/
theorem card_le_of_weight_le {C : Type u} [Fintype C]
    {compatible : C → C → Prop} {weight : C → ℕ}
    (selected : DistinguishedFamily compatible weight)
    (replacement : Finset C)
    (hreplacement : PairwiseCompatible compatible replacement)
    (hweight : familyWeight weight selected.family ≤
      familyWeight weight replacement) :
    selected.family.card ≤ replacement.card := by
  by_contra hnot
  have hcard : replacement.card < selected.family.card := by omega
  exact not_weight_ge_and_card_lt selected replacement hreplacement
    ⟨hweight, hcard⟩

/-! ## Model checks -/

/-- With one candidate of positive weight and universal compatibility, the
singleton is the unique weight-maximizing family. -/
theorem distinguishedFamily_singletonModel :
    ∃ selected : DistinguishedFamily (C := PUnit) (fun _ _ => True)
        (fun _ => 1),
      selected.family = {PUnit.unit} := by
  obtain ⟨selected⟩ := exists_distinguishedFamily (C := PUnit)
    (fun _ _ => True) (fun _ => 1)
  refine ⟨selected, ?_⟩
  have hsingletonCompatible :
      PairwiseCompatible (fun _ _ : PUnit => True) {PUnit.unit} := by
    intro _ _ _ _ _
    trivial
  have hweight := selected.weight_maximal {PUnit.unit} hsingletonCompatible
  have hmem : PUnit.unit ∈ selected.family := by
    by_contra hnot
    have hempty : selected.family = ∅ := by
      ext x
      have hx : x = PUnit.unit := Subsingleton.elim _ _
      rw [hx]
      constructor
      · intro h
        exact (hnot h).elim
      · intro h
        simp at h
    rw [hempty] at hweight
    simp [familyWeight] at hweight
  ext x
  have hx : x = PUnit.unit := Subsingleton.elim _ _
  rw [hx]
  simp only [hmem, Finset.mem_singleton]

/-- In the singleton model, the empty replacement has fewer members but
cannot preserve the selected positive weight. -/
theorem singletonModel_no_empty_replacement
    (selected : DistinguishedFamily (C := PUnit) (fun _ _ => True)
      (fun _ => 1)) (hselected : selected.family = {PUnit.unit}) :
    ¬ (familyWeight (fun _ : PUnit => 1) selected.family ≤
      familyWeight (fun _ : PUnit => 1) ∅) := by
  rw [hselected]
  simp [familyWeight]

end EstimatingSelection

end VanKampen
end GGT
end GroupApproximation
