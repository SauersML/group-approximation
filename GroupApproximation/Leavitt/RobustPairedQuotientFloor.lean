import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Fintype

/-!
# The robust paired-quotient floor after permutation repair

The exact paired-quotient obstruction has a quantitative finite counterpart.
Once the two diagonal transports have been repaired to permutations, changing
the left transport on `dV` labels and the right transport on `dW` labels can
change at most

`|W| * dV + |V| * dW`

entries of the crossed pairing table.  For a perfect binary pairing the
permuted table has `N * (N - 1) / 2` one-entries.  Combining this table bound
with the collision-repair estimates

`N * dV <= 4 * e00` and `N * dW <= 4 * e11`

gives the integer form

`N * (N - 1) <= 2 * e01 + 8 * e00 + 8 * e11`.

After division by `2*N^2`, this is exactly

`eps01 + 4*eps00 + 4*eps11 >= (N-1)/(2*N)`.

This file also constructs the permutation repairs canonically: it preserves
every singleton fiber and changes only collision sources.  Perfect row
separation gives the local collision charge.  The remaining combinatorial
step is the global summation of those local charges over the non-singleton
fibers; that budget is kept visible rather than silently assumed.
-/

namespace GroupApproximation
namespace RobustPairedQuotient

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

/-- The one-entries of a pairing table after applying maps to its two labels. -/
def oneSet (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) : Finset (V × W) :=
  (Finset.univ.product Finset.univ).filter fun p ↦ pair (R p.1) (L p.2)

/-- The labels on which two maps disagree. -/
def disagreementSet {X : Type*} [Fintype X] [DecidableEq X]
    (f g : X → X) : Finset X :=
  Finset.univ.filter fun x ↦ f x ≠ g x

/-- Sources lying in a non-singleton fiber of a finite map.  These are exactly
the sources which may have to move when the map is repaired to a
permutation. -/
def collisionSources {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) : Finset X :=
  Finset.univ.filter fun x ↦ ∃ y, y ≠ x ∧ f y = f x

@[simp] theorem mem_collisionSources {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (x : X) :
    x ∈ collisionSources f ↔ ∃ y, y ≠ x ∧ f y = f x := by
  simp [collisionSources]

/-- The restriction of a map to sources outside its collision set is
injective, so it extends to a permutation of the whole finite type. -/
theorem exists_permutation_agreeing_off_collisions
    {X : Type*} [Fintype X] [DecidableEq X] (f : X → X) :
    ∃ fbar : Equiv.Perm X, ∀ x, x ∉ collisionSources f → fbar x = f x := by
  let A := {x : X // x ∉ collisionSources f}
  let inclusion : A → X := fun x ↦ x.1
  let target : A → X := fun x ↦ f x.1
  have hinclusion : Function.Injective inclusion := by
    intro x y hxy
    exact Subtype.ext hxy
  have htarget : Function.Injective target := by
    intro x y hxy
    by_contra hne
    have hbase : y.1 ≠ x.1 := by
      intro hyx
      apply hne
      exact Subtype.ext hyx.symm
    apply x.2
    rw [mem_collisionSources]
    exact ⟨y.1, hbase, hxy.symm⟩
  obtain ⟨fbar, hfbar⟩ :=
    Equiv.Perm.exists_extending_pair inclusion target hinclusion htarget
  refine ⟨fbar, fun x hx ↦ ?_⟩
  exact hfbar ⟨x, hx⟩

/-- A fixed permutation repair which preserves every singleton fiber. -/
noncomputable def repairMap {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) : Equiv.Perm X :=
  Classical.choose (exists_permutation_agreeing_off_collisions f)

theorem repairMap_eq_of_not_collision
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (x : X) (hx : x ∉ collisionSources f) :
    repairMap f x = f x :=
  Classical.choose_spec (exists_permutation_agreeing_off_collisions f) x hx

/-- Repairing a finite map changes only sources in non-singleton fibers. -/
theorem disagreement_repairMap_subset_collisionSources
    {X : Type*} [Fintype X] [DecidableEq X] (f : X → X) :
    disagreementSet f (repairMap f) ⊆ collisionSources f := by
  intro x hx
  by_contra hcollision
  have hagree := repairMap_eq_of_not_collision f x hcollision
  have hne : f x ≠ repairMap f x := by
    simpa [disagreementSet] using hx
  exact hne hagree.symm

theorem card_disagreement_repairMap_le_collisionSources
    {X : Type*} [Fintype X] [DecidableEq X] (f : X → X) :
    (disagreementSet f (repairMap f)).card ≤ (collisionSources f).card :=
  Finset.card_le_card (disagreement_repairMap_subset_collisionSources f)

/-- A collision-source budget immediately gives the quantitative permutation
repair bound required by `robust_floor_of_permutation_repairs`. -/
theorem repairMap_disagreement_mul_le_of_collision_budget
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (N e : ℕ)
    (hbudget : N * (collisionSources f).card ≤ 4 * e) :
    N * (disagreementSet f (repairMap f)).card ≤ 4 * e := by
  exact (Nat.mul_le_mul_left N
    (card_disagreement_repairMap_le_collisionSources f)).trans hbudget

/-- Mismatches in one row of an approximate pairing transport. -/
def rowMismatchSet (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) (v : V) : Finset W :=
  Finset.univ.filter fun w ↦ pair (R v) (L w) ≠ pair v w

/-- Columns on which two rows of the original pairing differ. -/
def rowSeparationSet (pair : V → W → Prop) [DecidableRel pair]
    (v v' : V) : Finset W :=
  Finset.univ.filter fun w ↦ pair v w ≠ pair v' w

/-- If two transported row labels collide, every column separating the
original rows is charged to a mismatch in at least one of those two rows. -/
theorem rowSeparation_subset_mismatch_union_of_collision
    (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) {v v' : V}
    (hcollision : R v = R v') :
    rowSeparationSet pair v v' ⊆
      rowMismatchSet pair R L v ∪ rowMismatchSet pair R L v' := by
  intro w hw
  by_contra hmem
  have hv : pair (R v) (L w) = pair v w := by
    have := (Finset.not_mem_union.mp hmem).1
    simpa [rowMismatchSet] using this
  have hv' : pair (R v') (L w) = pair v' w := by
    have := (Finset.not_mem_union.mp hmem).2
    simpa [rowMismatchSet] using this
  have heq : pair v w = pair v' w :=
    hv.symm.trans ((congrArg (fun x ↦ pair x (L w)) hcollision).trans hv')
  have hne : pair v w ≠ pair v' w := by
    simpa [rowSeparationSet] using hw
  exact hne heq

theorem card_rowSeparation_le_mismatch_add_of_collision
    (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) {v v' : V}
    (hcollision : R v = R v') :
    (rowSeparationSet pair v v').card ≤
      (rowMismatchSet pair R L v).card +
        (rowMismatchSet pair R L v').card := by
  exact (Finset.card_le_card
    (rowSeparation_subset_mismatch_union_of_collision
      pair R L hcollision)).trans (Finset.card_union_le _ _)

/-- Local collision charge.  Under perfect row separation, two distinct
sources in the same transported fiber consume at least `N/2` row errors. -/
theorem collision_pair_charge
    (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) (N : ℕ) {v v' : V}
    (hne : v ≠ v') (hcollision : R v = R v')
    (hperfectRows : ∀ x y, x ≠ y →
      2 * (rowSeparationSet pair x y).card = N) :
    N ≤ 2 * ((rowMismatchSet pair R L v).card +
      (rowMismatchSet pair R L v').card) := by
  calc
    N = 2 * (rowSeparationSet pair v v').card :=
      (hperfectRows v v' hne).symm
    _ ≤ 2 * ((rowMismatchSet pair R L v).card +
        (rowMismatchSet pair R L v').card) :=
      Nat.mul_le_mul_left 2
        (card_rowSeparation_le_mismatch_add_of_collision
          pair R L hcollision)

/-- Pairs whose left or right label map differs from a proposed repair. -/
def changedPairs (R Rbar : V → V) (L Lbar : W → W) : Finset (V × W) :=
  (disagreementSet R Rbar).product Finset.univ ∪
    Finset.univ.product (disagreementSet L Lbar)

theorem oneSet_subset_oneSet_union_changedPairs
    (pair : V → W → Prop) [DecidableRel pair]
    (R Rbar : V → V) (L Lbar : W → W) :
    oneSet pair Rbar Lbar ⊆ oneSet pair R L ∪ changedPairs R Rbar L Lbar := by
  intro p hp
  by_cases hR : R p.1 = Rbar p.1
  · by_cases hL : L p.2 = Lbar p.2
    · apply Finset.mem_union_left
      simpa [oneSet, hR, hL] using hp
    · apply Finset.mem_union_right
      simp [changedPairs, disagreementSet, hL]
  · apply Finset.mem_union_right
    simp [changedPairs, disagreementSet, hR]

/-- A row repair on `dV` labels and a column repair on `dW` labels changes at
most `|W|*dV + |V|*dW` entries of the pairing table. -/
theorem card_oneSet_repaired_le
    (pair : V → W → Prop) [DecidableRel pair]
    (R Rbar : V → V) (L Lbar : W → W) :
    (oneSet pair Rbar Lbar).card ≤
      (oneSet pair R L).card +
        (disagreementSet R Rbar).card * Fintype.card W +
          Fintype.card V * (disagreementSet L Lbar).card := by
  calc
    (oneSet pair Rbar Lbar).card ≤
        (oneSet pair R L ∪ changedPairs R Rbar L Lbar).card :=
      Finset.card_le_card
        (oneSet_subset_oneSet_union_changedPairs pair R Rbar L Lbar)
    _ ≤ (oneSet pair R L).card + (changedPairs R Rbar L Lbar).card :=
      Finset.card_union_le _ _
    _ ≤ (oneSet pair R L).card +
        ((disagreementSet R Rbar).product (Finset.univ : Finset W)).card +
          ((Finset.univ : Finset V).product (disagreementSet L Lbar)).card := by
      simpa [changedPairs, Nat.add_assoc] using
        Nat.add_le_add_left
          (Finset.card_union_le
            ((disagreementSet R Rbar).product (Finset.univ : Finset W))
            ((Finset.univ : Finset V).product (disagreementSet L Lbar)))
          (oneSet pair R L).card
    _ = (oneSet pair R L).card +
        (disagreementSet R Rbar).card * Fintype.card W +
          Fintype.card V * (disagreementSet L Lbar).card := by
      simp

/-- Integer form of the robust Hamming floor.

`e01` is the crossed-table one count, while `e00,e11` are the two diagonal
mismatch counts.  The hypotheses `hR,hL` are exactly the output required from
the collision-repair lemma. -/
theorem robust_floor_of_permutation_repairs
    (pair : V → W → Prop) [DecidableRel pair]
    (R₀ Rbar₀ : V → V) (L₁ Lbar₁ : W → W)
    (N e₀₀ e₁₁ : ℕ)
    (hV : Fintype.card V = N) (hW : Fintype.card W = N)
    (hperfectCount :
      2 * (oneSet pair Rbar₀ Lbar₁).card = N * (N - 1))
    (hR : N * (disagreementSet R₀ Rbar₀).card ≤ 4 * e₀₀)
    (hL : N * (disagreementSet L₁ Lbar₁).card ≤ 4 * e₁₁) :
    N * (N - 1) ≤
      2 * (oneSet pair R₀ L₁).card + 8 * e₀₀ + 8 * e₁₁ := by
  have htable := card_oneSet_repaired_le pair R₀ Rbar₀ L₁ Lbar₁
  rw [hV, hW] at htable
  calc
    N * (N - 1) = 2 * (oneSet pair Rbar₀ Lbar₁).card :=
      hperfectCount.symm
    _ ≤ 2 * ((oneSet pair R₀ L₁).card +
        (disagreementSet R₀ Rbar₀).card * N +
          N * (disagreementSet L₁ Lbar₁).card) :=
      Nat.mul_le_mul_left 2 htable
    _ = 2 * (oneSet pair R₀ L₁).card +
        2 * (N * (disagreementSet R₀ Rbar₀).card) +
          2 * (N * (disagreementSet L₁ Lbar₁).card) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ ≤ 2 * (oneSet pair R₀ L₁).card +
        2 * (4 * e₀₀) + 2 * (4 * e₁₁) := by
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hR) _)
        (Nat.mul_le_mul_left 2 hL)
    _ = 2 * (oneSet pair R₀ L₁).card + 8 * e₀₀ + 8 * e₁₁ := by
      simp [Nat.mul_assoc]

/-- Robust floor using the canonical singleton-fiber repairs.  The only
unresolved hypotheses here are the two global collision-source budgets; no
existential choice of repaired permutations remains. -/
theorem robust_floor_of_collision_budgets
    (pair : V → W → Prop) [DecidableRel pair]
    (R₀ : V → V) (L₁ : W → W)
    (N e₀₀ e₁₁ : ℕ)
    (hV : Fintype.card V = N) (hW : Fintype.card W = N)
    (hperfectCount :
      2 * (oneSet pair (repairMap R₀) (repairMap L₁)).card = N * (N - 1))
    (hRcollision : N * (collisionSources R₀).card ≤ 4 * e₀₀)
    (hLcollision : N * (collisionSources L₁).card ≤ 4 * e₁₁) :
    N * (N - 1) ≤
      2 * (oneSet pair R₀ L₁).card + 8 * e₀₀ + 8 * e₁₁ := by
  apply robust_floor_of_permutation_repairs pair R₀ (repairMap R₀)
    L₁ (repairMap L₁) N e₀₀ e₁₁ hV hW hperfectCount
  · exact repairMap_disagreement_mul_le_of_collision_budget
      R₀ N e₀₀ hRcollision
  · exact repairMap_disagreement_mul_le_of_collision_budget
      L₁ N e₁₁ hLcollision

end RobustPairedQuotient
end GroupApproximation
