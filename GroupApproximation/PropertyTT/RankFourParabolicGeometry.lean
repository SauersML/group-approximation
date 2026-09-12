import GroupApproximation.Leavitt.RankFourCompressors
import GroupApproximation.PropertyT.ClassTwoNormalForm
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Rank-four row and column parabolics over an arbitrary ring

This file isolates the ring-independent algebra needed for `(TT)/T`
globalization.  The three last-column root groups and the three last-row root
groups admit three-factor normal forms, generate the rank-four elementary
group together, and are normalized by the stabilized rank-three elementary
group.  Everything is proved from the Steinberg relations.
-/

namespace GroupApproximation
namespace RankFourParabolicGeometry

open scoped commutatorElement Pointwise

noncomputable section

variable {R : Type*} [Ring R]

abbrev E4 := elementaryGroup (Fin 4) R

def X03 : Subgroup (E4 (R := R)) := elementaryRootSubgroup 0 3 (by decide)
def X13 : Subgroup (E4 (R := R)) := elementaryRootSubgroup 1 3 (by decide)
def X23 : Subgroup (E4 (R := R)) := elementaryRootSubgroup 2 3 (by decide)
def X30 : Subgroup (E4 (R := R)) := elementaryRootSubgroup 3 0 (by decide)
def X31 : Subgroup (E4 (R := R)) := elementaryRootSubgroup 3 1 (by decide)
def X32 : Subgroup (E4 (R := R)) := elementaryRootSubgroup 3 2 (by decide)

def columnPlane : Subgroup (E4 (R := R)) := X13 ⊔ X23
def columnGroup : Subgroup (E4 (R := R)) := X03 ⊔ columnPlane
def rowPlane : Subgroup (E4 (R := R)) := X31 ⊔ X32
def rowGroup : Subgroup (E4 (R := R)) := X30 ⊔ rowPlane

private theorem root_mem_centralizer_rootSubgroup
    {I : Type*} [Fintype I] [DecidableEq I]
    (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a : R) :
    elementaryRoot i j hij a ∈
      Subgroup.centralizer (elementaryRootSubgroup (R := R) k l hkl :
        Set (elementaryGroup I R)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  exact (elementaryRoot_commute_of_ne i j k l hij hkl hjk hli a b).eq.symm

private theorem root_mem_normalizer_rootSubgroup
    {I : Type*} [Fintype I] [DecidableEq I]
    (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a : R) :
    elementaryRoot i j hij a ∈
      Subgroup.normalizer (elementaryRootSubgroup k l hkl :
        Subgroup (elementaryGroup I R)) :=
  Subgroup.centralizer_le_normalizer _ <|
    root_mem_centralizer_rootSubgroup i j k l hij hkl hjk hli a

private theorem root_mem_normalizer_columnPair
    {I : Type*} [Fintype I] [DecidableEq I]
    (i j t : I) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (a : R) :
    elementaryRoot i j hij a ∈ Subgroup.normalizer
      (elementaryRootSubgroup i t hit ⊔ elementaryRootSubgroup j t hjt :
        Subgroup (elementaryGroup I R)) := by
  let Y := elementaryRootSubgroup (R := R) i j hij
  let X := elementaryRootSubgroup (R := R) j t hjt
  let Z := elementaryRootSubgroup (R := R) i t hit
  have hYX : ⁅Y, X⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [elementaryRoot_commutator i j t hij hjt hit x y]
    exact ⟨x * y, rfl⟩
  have hYZ : ⁅Y, Z⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [commutatorElement_eq_one_iff_commute.mpr
      (elementaryRoot_commute_of_ne i j i t hij hit hij.symm hit.symm x y)]
    exact Z.one_mem
  have h := ClassTwoNormalForm.le_normalizer_sup X Y Z hYX hYZ
  simpa only [sup_comm] using h ⟨a, rfl⟩

private theorem root_mem_normalizer_threeColumn
    (i j k t : Fin 4) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (hjk : j ≠ k) (_hki : k ≠ i) (hkt : k ≠ t) (a : R) :
    elementaryRoot i j hij a ∈ Subgroup.normalizer
      ((elementaryRootSubgroup i t hit ⊔ elementaryRootSubgroup j t hjt) ⊔
        elementaryRootSubgroup k t hkt : Subgroup (E4 (R := R))) := by
  have hp := root_mem_normalizer_columnPair i j t hij hit hjt a
  have hk := root_mem_normalizer_rootSubgroup i j k t hij hkt hjk hit.symm a
  exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup
    (elementaryRootSubgroup i t hit ⊔ elementaryRootSubgroup j t hjt)
    (elementaryRootSubgroup k t hkt) ⟨hp, hk⟩

private theorem rootSubgroup_le_normalizer_rowPair
    {I : Type*} [Fintype I] [DecidableEq I]
    (k i j : I) (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j) :
    elementaryRootSubgroup (R := R) i j hij ≤ Subgroup.normalizer
      (elementaryRootSubgroup k i hki ⊔ elementaryRootSubgroup k j hkj :
        Subgroup (elementaryGroup I R)) := by
  let X := elementaryRootSubgroup (R := R) k i hki
  let Y := elementaryRootSubgroup (R := R) i j hij
  let Z := elementaryRootSubgroup (R := R) k j hkj
  have hXY : ⁅X, Y⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨b, rfl⟩ _ ⟨a, rfl⟩
    rw [elementaryRoot_commutator k i j hki hij hkj b a]
    exact ⟨b * a, rfl⟩
  have hYX : ⁅Y, X⁆ ≤ Z :=
    by rw [Subgroup.commutator_comm]; exact hXY
  have hYZ : ⁅Y, Z⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [commutatorElement_eq_one_iff_commute.mpr
      (elementaryRoot_commute_of_ne i j k j hij hkj hkj.symm hij.symm a b)]
    exact Z.one_mem
  exact ClassTwoNormalForm.le_normalizer_sup X Y Z hYX hYZ

private theorem root_mem_normalizer_threeRow
    (t i j k : Fin 4) (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k)
    (hij : i ≠ j) (_hjk : j ≠ k) (hki : k ≠ i) (a : R) :
    elementaryRoot i j hij a ∈ Subgroup.normalizer
      ((elementaryRootSubgroup t i hti ⊔ elementaryRootSubgroup t j htj) ⊔
        elementaryRootSubgroup t k htk : Subgroup (E4 (R := R))) := by
  have hp := rootSubgroup_le_normalizer_rowPair t i j hti htj hij
    (show elementaryRoot i j hij a ∈ elementaryRootSubgroup i j hij from ⟨a, rfl⟩)
  have hk := root_mem_normalizer_rootSubgroup i j t k hij htk
    (by exact htj.symm) (by exact hki) a
  exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup
    (elementaryRootSubgroup t i hti ⊔ elementaryRootSubgroup t j htj)
    (elementaryRootSubgroup t k htk) ⟨hp, hk⟩

theorem coreRoot_mem_normalizer_columnGroup
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    elementaryRoot (RankFour.coreIndex i) (RankFour.coreIndex j)
        (RankFour.coreIndex_injective.ne hij) a ∈
      Subgroup.normalizer (columnGroup (R := R)) := by
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  next => simpa [RankFour.Index, RankFour.coreIndex, columnGroup, columnPlane, X03, X13, X23, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeColumn (R := R) 0 1 2 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, columnGroup, columnPlane, X03, X13, X23, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeColumn (R := R) 0 2 1 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, columnGroup, columnPlane, X03, X13, X23, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeColumn (R := R) 1 0 2 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, columnGroup, columnPlane, X03, X13, X23, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeColumn (R := R) 1 2 0 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, columnGroup, columnPlane, X03, X13, X23, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeColumn (R := R) 2 0 1 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, columnGroup, columnPlane, X03, X13, X23, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeColumn (R := R) 2 1 0 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)

theorem coreRoot_mem_normalizer_rowGroup
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    elementaryRoot (RankFour.coreIndex i) (RankFour.coreIndex j)
        (RankFour.coreIndex_injective.ne hij) a ∈
      Subgroup.normalizer (rowGroup (R := R)) := by
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  next => simpa [RankFour.Index, RankFour.coreIndex, rowGroup, rowPlane, X30, X31, X32, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeRow (R := R) 3 0 1 2
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, rowGroup, rowPlane, X30, X31, X32, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeRow (R := R) 3 0 2 1
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, rowGroup, rowPlane, X30, X31, X32, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeRow (R := R) 3 1 0 2
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, rowGroup, rowPlane, X30, X31, X32, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeRow (R := R) 3 1 2 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, rowGroup, rowPlane, X30, X31, X32, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeRow (R := R) 3 2 0 1
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)
  next => simpa [RankFour.Index, RankFour.coreIndex, rowGroup, rowPlane, X30, X31, X32, sup_assoc,
      sup_comm, sup_left_comm] using
      (root_mem_normalizer_threeRow (R := R) 3 2 1 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a)

private theorem core_transvections_generate :
    Subgroup.closure
      {z : RankFour.Core R |
        ∃ (i j : Fin 3) (hij : i ≠ j) (a : R),
          RankFour.coreTransvection i j hij a = z} = ⊤ := by
  apply top_unique
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩
  | one => exact (Subgroup.closure _).one_mem
  | mul x y hxmem hymem hx hy =>
      exact (Subgroup.closure _).mul_mem hx hy
  | inv x hxmem hx =>
      exact (Subgroup.closure _).inv_mem hx

private theorem coreEmbedding_mem_subgroup_of_roots
    (K : Subgroup (E4 (R := R)))
    (hroot : ∀ (i j : Fin 3) (hij : i ≠ j) (a : R),
      elementaryRoot (RankFour.coreIndex i) (RankFour.coreIndex j)
        (RankFour.coreIndex_injective.ne hij) a ∈ K)
    (g : RankFour.Core R) : RankFour.coreEmbedding g ∈ K := by
  have hroots :
      {z : RankFour.Core R |
        ∃ (i j : Fin 3) (hij : i ≠ j) (a : R),
          RankFour.coreTransvection i j hij a = z} ⊆
        K.comap RankFour.coreEmbedding := by
    rintro z ⟨i, j, hij, a, rfl⟩
    change RankFour.coreEmbedding (RankFour.coreTransvection i j hij a) ∈ K
    rw [RankFour.coreEmbedding_coreTransvection]
    exact hroot i j hij a
  have hle := (Subgroup.closure_le (K.comap RankFour.coreEmbedding)).2 hroots
  rw [core_transvections_generate (R := R)] at hle
  exact hle (by simp)

/-- The entire stabilized rank-three elementary group normalizes the last
column parabolic. -/
theorem coreEmbedding_mem_normalizer_columnGroup
    (g : RankFour.Core R) :
    RankFour.coreEmbedding g ∈ Subgroup.normalizer (columnGroup (R := R)) :=
  coreEmbedding_mem_subgroup_of_roots
    (Subgroup.normalizer (columnGroup (R := R) : Set (E4 (R := R))))
    (coreRoot_mem_normalizer_columnGroup (R := R)) g

/-- The entire stabilized rank-three elementary group normalizes the last
row parabolic. -/
theorem coreEmbedding_mem_normalizer_rowGroup
    (g : RankFour.Core R) :
    RankFour.coreEmbedding g ∈ Subgroup.normalizer (rowGroup (R := R)) :=
  coreEmbedding_mem_subgroup_of_roots
    (Subgroup.normalizer (rowGroup (R := R) : Set (E4 (R := R))))
    (coreRoot_mem_normalizer_rowGroup (R := R)) g

private theorem exists_two_roots_of_mem_sup
    {I : Type*} [Fintype I] [DecidableEq I]
    (i j k : I) (hik : i ≠ k) (hjk : j ≠ k)
    {g : elementaryGroup I R}
    (hg : g ∈ elementaryRootSubgroup i k hik ⊔
      elementaryRootSubgroup j k hjk) :
    ∃ a b : R, elementaryRoot i k hik a * elementaryRoot j k hjk b = g := by
  have hnorm : elementaryRootSubgroup (R := R) i k hik ≤
      Subgroup.normalizer (elementaryRootSubgroup j k hjk :
        Subgroup (elementaryGroup I R)) := by
    intro _
    rintro ⟨a, rfl⟩
    exact root_mem_normalizer_rootSubgroup i k j k hik hjk
      (by exact hjk.symm) (by exact hik.symm) a
  have hgset : g ∈ (↑(elementaryRootSubgroup (R := R) i k hik ⊔
      elementaryRootSubgroup j k hjk) : Set (elementaryGroup I R)) := by
    exact hg
  rw [show (↑(elementaryRootSubgroup (R := R) i k hik ⊔
        elementaryRootSubgroup j k hjk) : Set (elementaryGroup I R)) =
      (elementaryRootSubgroup (R := R) i k hik : Set (elementaryGroup I R)) *
        (elementaryRootSubgroup (R := R) j k hjk : Set (elementaryGroup I R)) from
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hgset
  rcases hgset with ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
  exact ⟨a, b, rfl⟩

/-- Every last-column element is a product of its three root coordinates. -/
theorem exists_three_column_roots {g : E4 (R := R)}
    (hg : g ∈ columnGroup (R := R)) :
    ∃ a b c : R,
      elementaryRoot (0 : Fin 4) 3 (by decide) a *
        elementaryRoot (1 : Fin 4) 3 (by decide) b *
          elementaryRoot (2 : Fin 4) 3 (by decide) c = g := by
  have hnorm : X03 (R := R) ≤ Subgroup.normalizer (columnPlane (R := R)) := by
    intro _
    rintro ⟨a, rfl⟩
    have h13 := root_mem_normalizer_rootSubgroup (R := R)
      (0 : Fin 4) 3 1 3 (by decide) (by decide) (by decide) (by decide) a
    have h23 := root_mem_normalizer_rootSubgroup (R := R)
      (0 : Fin 4) 3 2 3 (by decide) (by decide) (by decide) (by decide) a
    exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨h13, h23⟩
  have hgset : g ∈ (↑(X03 (R := R) ⊔ columnPlane (R := R)) : Set (E4 (R := R))) := hg
  rw [show (↑(X03 (R := R) ⊔ columnPlane (R := R)) : Set (E4 (R := R))) =
      (X03 (R := R) : Set (E4 (R := R))) *
        (columnPlane (R := R) : Set (E4 (R := R))) from
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hgset
  rcases hgset with ⟨_, ⟨a, rfl⟩, p, hp, rfl⟩
  obtain ⟨b, c, rfl⟩ := exists_two_roots_of_mem_sup 1 2 3
    (by decide) (by decide) hp
  exact ⟨a, b, c, by simp [mul_assoc]⟩

/-- Every last-row element is a product of its three root coordinates. -/
theorem exists_three_row_roots {g : E4 (R := R)}
    (hg : g ∈ rowGroup (R := R)) :
    ∃ a b c : R,
      elementaryRoot (3 : Fin 4) 0 (by decide) a *
        elementaryRoot (3 : Fin 4) 1 (by decide) b *
          elementaryRoot (3 : Fin 4) 2 (by decide) c = g := by
  -- Common-row roots commute, so the same two-stage pointwise product
  -- argument as for the column applies after exchanging the index roles.
  have hnormPlane : X31 (R := R) ≤ Subgroup.normalizer (X32 (R := R)) := by
    intro _
    rintro ⟨a, rfl⟩
    exact root_mem_normalizer_rootSubgroup (R := R)
      (3 : Fin 4) 1 3 2 (by decide) (by decide)
      (by decide) (by decide) a
  have hpFact : ∀ {p : E4 (R := R)}, p ∈ rowPlane (R := R) →
      ∃ b c : R, elementaryRoot (3 : Fin 4) 1 (by decide) b *
        elementaryRoot (3 : Fin 4) 2 (by decide) c = p := by
    intro p hp
    have hpset : p ∈ (↑(X31 (R := R) ⊔ X32 (R := R)) : Set (E4 (R := R))) := hp
    rw [show (↑(X31 (R := R) ⊔ X32 (R := R)) : Set (E4 (R := R))) =
        (X31 (R := R) : Set (E4 (R := R))) * (X32 (R := R) : Set (E4 (R := R))) from
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormPlane] at hpset
    rcases hpset with ⟨_, ⟨b, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨b, c, rfl⟩
  have hnorm : X30 (R := R) ≤ Subgroup.normalizer (rowPlane (R := R)) := by
    intro _
    rintro ⟨a, rfl⟩
    have h31 := root_mem_normalizer_rootSubgroup (R := R)
      (3 : Fin 4) 0 3 1
      (by decide) (by decide) (by decide) (by decide) a
    have h32 := root_mem_normalizer_rootSubgroup (R := R)
      (3 : Fin 4) 0 3 2
      (by decide) (by decide) (by decide) (by decide) a
    exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨h31, h32⟩
  have hgset : g ∈ (↑(X30 (R := R) ⊔ rowPlane (R := R)) : Set (E4 (R := R))) := hg
  rw [show (↑(X30 (R := R) ⊔ rowPlane (R := R)) : Set (E4 (R := R))) =
      (X30 (R := R) : Set (E4 (R := R))) * (rowPlane (R := R) : Set (E4 (R := R))) from
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hgset
  rcases hgset with ⟨_, ⟨a, rfl⟩, p, hp, rfl⟩
  obtain ⟨b, c, rfl⟩ := hpFact hp
  exact ⟨a, b, c, by simp [mul_assoc]⟩

private theorem root_to_last_mem_columnGroup
    (i : Fin 4) (hi : i ≠ 3) (a : R) :
    elementaryRoot i 3 hi a ∈ columnGroup (R := R) := by
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (show X03 (R := R) ≤ columnGroup (R := R) from
      le_sup_left) ⟨a, rfl⟩
  · exact (show columnPlane (R := R) ≤ columnGroup (R := R) from
      le_sup_right) ((show X13 (R := R) ≤ columnPlane (R := R) from
        le_sup_left) ⟨a, rfl⟩)
  · exact (show columnPlane (R := R) ≤ columnGroup (R := R) from
      le_sup_right) ((show X23 (R := R) ≤ columnPlane (R := R) from
        le_sup_right) ⟨a, rfl⟩)

private theorem root_from_last_mem_rowGroup
    (j : Fin 4) (hj : 3 ≠ j) (a : R) :
    elementaryRoot 3 j hj a ∈ rowGroup (R := R) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (show X30 (R := R) ≤ rowGroup (R := R) from
      le_sup_left) ⟨a, rfl⟩
  · exact (show rowPlane (R := R) ≤ rowGroup (R := R) from
      le_sup_right) ((show X31 (R := R) ≤ rowPlane (R := R) from
        le_sup_left) ⟨a, rfl⟩)
  · exact (show rowPlane (R := R) ≤ rowGroup (R := R) from
      le_sup_right) ((show X32 (R := R) ≤ rowPlane (R := R) from
        le_sup_right) ⟨a, rfl⟩)

/-- The union of the last-column and last-row parabolics generates `EL₄`. -/
theorem column_row_generate :
    Subgroup.closure ((columnGroup (R := R) : Set (E4 (R := R))) ∪
      (rowGroup (R := R) : Set (E4 (R := R)))) = ⊤ := by
  apply top_unique
  rw [← elementaryRootSet_generate (I := Fin 4) (R := R)]
  rw [Subgroup.closure_le]
  rintro g ⟨i, j, hij, a, rfl⟩
  by_cases hi : i = 3
  · subst i
    exact Subgroup.subset_closure
      (Or.inr (root_from_last_mem_rowGroup j hij a))
  by_cases hj : j = 3
  · subst j
    exact Subgroup.subset_closure
      (Or.inl (root_to_last_mem_columnGroup i hi a))
  have hit : i ≠ (3 : Fin 4) := hi
  have htj : (3 : Fin 4) ≠ j := Ne.symm hj
  have hx : elementaryRoot i 3 hit a ∈
      Subgroup.closure ((columnGroup (R := R) : Set (E4 (R := R))) ∪
        (rowGroup (R := R) : Set (E4 (R := R)))) :=
    Subgroup.subset_closure (Or.inl (root_to_last_mem_columnGroup i hit a))
  have hy : elementaryRoot 3 j htj 1 ∈
      Subgroup.closure ((columnGroup (R := R) : Set (E4 (R := R))) ∪
        (rowGroup (R := R) : Set (E4 (R := R)))) :=
    Subgroup.subset_closure (Or.inr (root_from_last_mem_rowGroup j htj 1))
  have hcomm := elementaryRoot_commutator i 3 j hit htj hij a 1
  rw [mul_one] at hcomm
  rw [← hcomm]
  let H := Subgroup.closure ((columnGroup (R := R) : Set (E4 (R := R))) ∪
    (rowGroup (R := R) : Set (E4 (R := R))))
  change ⁅elementaryRoot i 3 hit a, elementaryRoot 3 j htj 1⁆ ∈ H
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

end
end RankFourParabolicGeometry
end GroupApproximation
