import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

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
separation gives the local collision charge.  Double counting all ordered
off-diagonal pairs in each non-singleton fiber gives the sharp global repair
budget, so the deterministic robust floor is proved end to end.
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

omit [Fintype V] [DecidableEq V] in
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
  simp only [Finset.mem_union, not_or] at hmem
  have hv : pair (R v) (L w) = pair v w := by
    have := hmem.1
    simpa [rowMismatchSet] using this
  have hv' : pair (R v') (L w) = pair v' w := by
    have := hmem.2
    simpa [rowMismatchSet] using this
  have heq : pair v w = pair v' w :=
    hv.symm.trans ((congrArg (fun x ↦ pair x (L w)) hcollision).trans hv')
  have hne : pair v w ≠ pair v' w := by
    simpa [rowSeparationSet] using hw
  exact hne heq

omit [Fintype V] [DecidableEq V] in
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

omit [Fintype V] [DecidableEq V] in
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

/-- The fiber of a finite self-map over one target. -/
def mapFiber {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (y : X) : Finset X :=
  Finset.univ.filter fun x ↦ f x = y

@[simp] theorem mem_mapFiber {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (x y : X) :
    x ∈ mapFiber f y ↔ f x = y := by
  simp [mapFiber]

/-- Targets whose fibers contain at least two sources. -/
def collisionTargets {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) : Finset X :=
  Finset.univ.filter fun y ↦ 1 < (mapFiber f y).card

@[simp] theorem mem_collisionTargets
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (y : X) :
    y ∈ collisionTargets f ↔ 1 < (mapFiber f y).card := by
  simp [collisionTargets]

/-- A source is a collision source exactly when its image is a collision
target. -/
theorem mem_collisionSources_iff_image_mem_collisionTargets
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (x : X) :
    x ∈ collisionSources f ↔ f x ∈ collisionTargets f := by
  rw [mem_collisionSources, mem_collisionTargets]
  constructor
  · rintro ⟨y, hyx, hfy⟩
    rw [Finset.one_lt_card]
    exact ⟨x, by simp [mapFiber], y, by simpa [mapFiber] using hfy, hyx.symm⟩
  · intro hcard
    rw [Finset.one_lt_card] at hcard
    obtain ⟨a, ha, b, hb, hab⟩ := hcard
    have hfa : f a = f x := by simpa [mapFiber] using ha
    have hfb : f b = f x := by simpa [mapFiber] using hb
    by_cases hax : a = x
    · refine ⟨b, ?_, hfb⟩
      intro hbx
      exact hab (hax.trans hbx.symm)
    · exact ⟨a, hax, hfa⟩

/-- Collision sources are partitioned by the non-singleton fibers. -/
theorem card_collisionSources_eq_sum_mapFiber
    {X : Type*} [Fintype X] [DecidableEq X] (f : X → X) :
    (collisionSources f).card =
      ∑ y ∈ collisionTargets f, (mapFiber f y).card := by
  have hfilter : collisionSources f =
      Finset.univ.filter fun x ↦ f x ∈ collisionTargets f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_collisionSources_iff_image_mem_collisionTargets f x
  calc
    (collisionSources f).card =
        (Finset.univ.filter fun x ↦ f x ∈ collisionTargets f).card :=
      congrArg Finset.card hfilter
    _ = ∑ y ∈ collisionTargets f, (mapFiber f y).card := by
      simpa [mapFiber] using
        (Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset X) (collisionTargets f) f).symm

/-- Exact double counting on an off-diagonal square.  Each value `cost x`
occurs once in the first and once in the second coordinate for each of the
other `|F|-1` elements. -/
theorem sum_offDiag_pairCost
    {X : Type*} [DecidableEq X]
    (F : Finset X) (cost : X → ℕ) :
    ∑ p ∈ F.offDiag, (cost p.1 + cost p.2) =
      2 * (F.card - 1) * ∑ x ∈ F, cost x := by
  have hsplit :
      (∑ p ∈ F.diag, (cost p.1 + cost p.2)) +
          (∑ p ∈ F.offDiag, (cost p.1 + cost p.2)) =
        ∑ p ∈ F ×ˢ F, (cost p.1 + cost p.2) := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag F),
      Finset.diag_union_offDiag]
  have hdiag :
      ∑ p ∈ F.diag, (cost p.1 + cost p.2) =
        2 * ∑ x ∈ F, cost x := by
    simp [Finset.sum_diag, Finset.sum_add_distrib, Nat.two_mul]
  have hproduct :
      ∑ p ∈ F ×ˢ F, (cost p.1 + cost p.2) =
        2 * F.card * ∑ x ∈ F, cost x := by
    rw [Finset.sum_product]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  by_cases hF : F.Nonempty
  · have hcard : F.card = (F.card - 1) + 1 := by
      have hone : 1 ≤ F.card := Finset.one_le_card.mpr hF
      omega
    rw [hdiag, hproduct, hcard] at hsplit
    simp [Nat.add_mul, Nat.mul_add] at hsplit
    omega
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [this]

/-- Summing the pair charge over every ordered off-diagonal pair in one
non-singleton fiber gives the optimal factor-four fiber budget. -/
theorem fiber_collision_budget
    {X : Type*} [DecidableEq X]
    (F : Finset X) (cost : X → ℕ) (N : ℕ)
    (hF : 1 < F.card)
    (hcharge : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      N ≤ 2 * (cost x + cost y)) :
    N * F.card ≤ 4 * ∑ x ∈ F, cost x := by
  have hsum :
      ∑ p ∈ F.offDiag, N ≤
        ∑ p ∈ F.offDiag, 2 * (cost p.1 + cost p.2) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpdata := (Finset.mem_offDiag.mp hp)
    exact hcharge p.1 hpdata.1 p.2 hpdata.2.1 hpdata.2.2
  have hoffcard : F.offDiag.card = F.card * (F.card - 1) := by
    rw [Finset.offDiag_card]
    rw [Nat.mul_sub_left_distrib]
    simp
  have hsum' :
      F.offDiag.card * N ≤
        2 * ∑ p ∈ F.offDiag, (cost p.1 + cost p.2) := by
    simpa [Finset.mul_sum] using hsum
  have hfactor :
      (F.card - 1) * (N * F.card) ≤
        (F.card - 1) * (4 * ∑ x ∈ F, cost x) := by
    rw [hoffcard, sum_offDiag_pairCost F cost] at hsum'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum'
  exact Nat.le_of_mul_le_mul_left hfactor (by omega)

/-- The total row mismatch count of a deterministic pairing transport. -/
def totalRowMismatch (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) : ℕ :=
  ∑ v, (rowMismatchSet pair R L v).card

/-- The local pair charge supplies the factor-four budget on every collision
fiber of the transported row map. -/
theorem mapFiber_collision_budget
    (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) (N : ℕ)
    (hperfectRows : ∀ x y, x ≠ y →
      2 * (rowSeparationSet pair x y).card = N)
    (z : V) (hz : z ∈ collisionTargets R) :
    N * (mapFiber R z).card ≤
      4 * ∑ v ∈ mapFiber R z, (rowMismatchSet pair R L v).card := by
  apply fiber_collision_budget (mapFiber R z)
    (fun v ↦ (rowMismatchSet pair R L v).card) N
  · simpa using (mem_collisionTargets R z).mp hz
  · intro x hx y hy hxy
    apply collision_pair_charge pair R L N hxy
    · have hxz := (mem_mapFiber R x z).mp hx
      have hyz := (mem_mapFiber R y z).mp hy
      exact hxz.trans hyz.symm
    · exact hperfectRows

/-- Global collision repair budget.  This is the finite-fiber summation step:
the non-singleton fibers partition the collision sources, and fiberwise row
errors form a sub-sum of the total diagonal mismatch. -/
theorem collisionSources_mul_le_totalRowMismatch
    (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) (N : ℕ)
    (hperfectRows : ∀ x y, x ≠ y →
      2 * (rowSeparationSet pair x y).card = N) :
    N * (collisionSources R).card ≤ 4 * totalRowMismatch pair R L := by
  rw [card_collisionSources_eq_sum_mapFiber]
  calc
    N * ∑ z ∈ collisionTargets R, (mapFiber R z).card =
        ∑ z ∈ collisionTargets R, N * (mapFiber R z).card := by
      simp [Finset.mul_sum]
    _ ≤ ∑ z ∈ collisionTargets R,
        4 * ∑ v ∈ mapFiber R z,
          (rowMismatchSet pair R L v).card := by
      apply Finset.sum_le_sum
      intro z hz
      exact mapFiber_collision_budget pair R L N hperfectRows z hz
    _ = 4 * ∑ z ∈ collisionTargets R,
        ∑ v ∈ mapFiber R z, (rowMismatchSet pair R L v).card := by
      simp [Finset.mul_sum]
    _ ≤ 4 * totalRowMismatch pair R L := by
      apply Nat.mul_le_mul_left 4
      have hpartial := Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg
        (s := (Finset.univ : Finset V)) (t := collisionTargets R)
        (g := R) (f := fun v ↦ (rowMismatchSet pair R L v).card)
        (fun _ _ ↦ Nat.zero_le _)
      simpa [mapFiber, totalRowMismatch] using hpartial

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
      ring
    _ ≤ 2 * (oneSet pair R₀ L₁).card +
        2 * (4 * e₀₀) + 2 * (4 * e₁₁) := by
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hR) _)
        (Nat.mul_le_mul_left 2 hL)
    _ = 2 * (oneSet pair R₀ L₁).card + 8 * e₀₀ + 8 * e₁₁ := by
      ring

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

/-- The pairing with its two label spaces exchanged. -/
def transposePair (pair : V → W → Prop) : W → V → Prop :=
  fun w v ↦ pair v w

instance transposePair_decidableRel (pair : V → W → Prop)
    [DecidableRel pair] : DecidableRel (transposePair pair) :=
  fun w v ↦ inferInstanceAs (Decidable (pair v w))

/-- Full deterministic robust paired-quotient floor.  Perfect row separation
controls collisions of `R₀`; perfect column separation is the same row
statement for the transposed pairing and controls collisions of `L₁`.
The two diagonal errors are now concrete total mismatch counts rather than
abstract repair budgets. -/
theorem robust_deterministic_floor
    (pair : V → W → Prop) [DecidableRel pair]
    (R₀ R₁ : V → V) (L₀ L₁ : W → W) (N : ℕ)
    (hV : Fintype.card V = N) (hW : Fintype.card W = N)
    (hperfectRows : ∀ x y, x ≠ y →
      2 * (rowSeparationSet pair x y).card = N)
    (hperfectColumns : ∀ x y, x ≠ y →
      2 * (rowSeparationSet (transposePair pair) x y).card = N)
    (hperfectCount :
      2 * (oneSet pair (repairMap R₀) (repairMap L₁)).card = N * (N - 1)) :
    N * (N - 1) ≤
      2 * (oneSet pair R₀ L₁).card +
        8 * totalRowMismatch pair R₀ L₀ +
          8 * totalRowMismatch (transposePair pair) L₁ R₁ := by
  apply robust_floor_of_collision_budgets pair R₀ L₁ N
    (totalRowMismatch pair R₀ L₀)
    (totalRowMismatch (transposePair pair) L₁ R₁)
    hV hW hperfectCount
  · exact collisionSources_mul_le_totalRowMismatch
      pair R₀ L₀ N hperfectRows
  · exact collisionSources_mul_le_totalRowMismatch
      (transposePair pair) L₁ R₁ N hperfectColumns

/-! ## Independent bistochastic kernels

Separate doubly stochastic block-mass kernels are stronger than the
deterministic repair hypotheses: after averaging over the source labels, each
target label is uniform.  Hence independently sampled left and right targets
have the exact perfect-pairing one mass.  This observation is useful mainly
as a guardrail.  A matrix microstate generally supplies a correlated
four-index transport, not the product of its two block-mass marginals. -/

/-- Unnormalized one mass for independently sampled target labels after
averaging over all source labels.  The two parenthesized sums are the target
column masses of the two kernels. -/
def independentKernelOneMass
    (pair : V → W → Prop) [DecidableRel pair]
    (K : Matrix V V ℝ) (L : Matrix W W ℝ) : ℝ :=
  ∑ x, ∑ y,
    (∑ v, K v x) * (∑ w, L w y) * if pair x y then 1 else 0

/-- Independent doubly stochastic transports preserve the total one mass of
the original pairing table exactly. -/
theorem independentKernelOneMass_eq_oneSet_card
    (pair : V → W → Prop) [DecidableRel pair]
    (K : Matrix V V ℝ) (L : Matrix W W ℝ)
    (hK : K ∈ doublyStochastic ℝ V)
    (hL : L ∈ doublyStochastic ℝ W) :
    independentKernelOneMass pair K L =
      ((oneSet pair id id).card : ℝ) := by
  simp_rw [independentKernelOneMass,
    sum_col_of_mem_doublyStochastic hK,
    sum_col_of_mem_doublyStochastic hL]
  simp only [one_mul]
  change (∑ x, ∑ y, if pair x y then 1 else 0) =
    ((oneSet pair id id).card : ℝ)
  rw [← Fintype.sum_prod_type']
  simp [oneSet]

/-- For a perfect binary pairing, the independent bistochastic crossed mass
is exactly `N(N-1)/2`; no diagonal repair estimate is needed. -/
theorem independentKernelOneMass_perfect
    (pair : V → W → Prop) [DecidableRel pair]
    (K : Matrix V V ℝ) (L : Matrix W W ℝ) (N : ℕ)
    (hK : K ∈ doublyStochastic ℝ V)
    (hL : L ∈ doublyStochastic ℝ W)
    (hperfectCount : 2 * (oneSet pair id id).card = N * (N - 1)) :
    2 * independentKernelOneMass pair K L =
      ((N * (N - 1) : ℕ) : ℝ) := by
  rw [independentKernelOneMass_eq_oneSet_card pair K L hK hL]
  exact_mod_cast hperfectCount

/-! ## Averaging over one common classical latent map

The deterministic theorem extends to correlations only when all three
observed transport pairs come from the same latent map quadruple.  The next
theorem records that exact sufficient condition without imposing an
unjustified product factorization on the pairwise couplings. -/

/-- Weighted average of a natural-valued statistic on a finite latent
probability space. -/
def weightedNatAverage {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (f : Ω → ℕ) : ℝ :=
  ∑ ω, μ ω * f ω

theorem weightedNatAverage_mono
    {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (f g : Ω → ℕ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hfg : ∀ ω, f ω ≤ g ω) :
    weightedNatAverage μ f ≤ weightedNatAverage μ g := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfg ω) (hμ ω)

/-- Weighted average of a real-valued statistic on a finite latent
probability space. -/
def weightedRealAverage {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ ω * f ω

theorem weightedRealAverage_mono
    {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (f g : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hfg : ∀ ω, f ω ≤ g ω) :
    weightedRealAverage μ f ≤ weightedRealAverage μ g := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hfg ω) (hμ ω)

/-- Uniform pointwise error floors survive disintegration over fibers of
different finite ranks.  In the paired-quotient application `1/4` is the
minimum of `(N-1)/(2*N)` over every nonzero binary fiber (`N ≥ 2`). -/
theorem one_fourth_le_weighted_three_error
    {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (e₀₁ e₀₀ e₁₁ : Ω → ℝ)
    (hμnonneg : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (hfloor : ∀ ω, (1 : ℝ) / 4 ≤ e₀₁ ω + 4 * e₀₀ ω + 4 * e₁₁ ω) :
    (1 : ℝ) / 4 ≤
      weightedRealAverage μ e₀₁ +
        4 * weightedRealAverage μ e₀₀ +
          4 * weightedRealAverage μ e₁₁ := by
  have havg := weightedRealAverage_mono μ
    (fun _ ↦ (1 : ℝ) / 4)
    (fun ω ↦ e₀₁ ω + 4 * e₀₀ ω + 4 * e₁₁ ω)
    hμnonneg hfloor
  have hconstant : weightedRealAverage μ (fun _ ↦ (1 : ℝ) / 4) =
      (1 : ℝ) / 4 := by
    simp [weightedRealAverage, ← Finset.sum_mul, hμsum]
  have hscale (f : Ω → ℝ) :
      weightedRealAverage μ (fun ω ↦ 4 * f ω) =
        4 * weightedRealAverage μ f := by
    unfold weightedRealAverage
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [hconstant] at havg
  calc
    (1 : ℝ) / 4 ≤ weightedRealAverage μ
        (fun ω ↦ e₀₁ ω + 4 * e₀₀ ω + 4 * e₁₁ ω) := havg
    _ = weightedRealAverage μ e₀₁ +
        4 * weightedRealAverage μ e₀₀ +
          4 * weightedRealAverage μ e₁₁ := by
      calc
        _ = weightedRealAverage μ e₀₁ +
            weightedRealAverage μ (fun ω ↦ 4 * e₀₀ ω) +
              weightedRealAverage μ (fun ω ↦ 4 * e₁₁ ω) := by
          simp only [weightedRealAverage, mul_add, Finset.sum_add_distrib]
        _ = _ := by rw [hscale e₀₀, hscale e₁₁]

/-- Averaged robust floor for one common classical law on four map-valued
transports.  This is the precise classicalization endpoint needed from the
matrix-coordinate extraction: all three errors use the same latent `ω`. -/
theorem robust_floor_of_common_latent_maps
    {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ)
    (pair : V → W → Prop) [DecidableRel pair]
    (R₀ R₁ : Ω → V → V) (L₀ L₁ : Ω → W → W) (N : ℕ)
    (hμnonneg : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (hV : Fintype.card V = N) (hW : Fintype.card W = N)
    (hperfectRows : ∀ x y, x ≠ y →
      2 * (rowSeparationSet pair x y).card = N)
    (hperfectColumns : ∀ x y, x ≠ y →
      2 * (rowSeparationSet (transposePair pair) x y).card = N)
    (hperfectCount : ∀ ω,
      2 * (oneSet pair (repairMap (R₀ ω)) (repairMap (L₁ ω))).card =
        N * (N - 1)) :
    ((N * (N - 1) : ℕ) : ℝ) ≤
      2 * weightedNatAverage μ
        (fun ω ↦ (oneSet pair (R₀ ω) (L₁ ω)).card) +
      8 * weightedNatAverage μ
        (fun ω ↦ totalRowMismatch pair (R₀ ω) (L₀ ω)) +
      8 * weightedNatAverage μ
        (fun ω ↦ totalRowMismatch (transposePair pair) (L₁ ω) (R₁ ω)) := by
  have hpointwise : ∀ ω,
      N * (N - 1) ≤
        2 * (oneSet pair (R₀ ω) (L₁ ω)).card +
        8 * totalRowMismatch pair (R₀ ω) (L₀ ω) +
        8 * totalRowMismatch (transposePair pair) (L₁ ω) (R₁ ω) := by
    intro ω
    exact robust_deterministic_floor pair (R₀ ω) (R₁ ω) (L₀ ω) (L₁ ω)
      N hV hW hperfectRows hperfectColumns (hperfectCount ω)
  have havg := weightedNatAverage_mono μ
    (fun _ ↦ N * (N - 1))
    (fun ω ↦
      2 * (oneSet pair (R₀ ω) (L₁ ω)).card +
      8 * totalRowMismatch pair (R₀ ω) (L₀ ω) +
      8 * totalRowMismatch (transposePair pair) (L₁ ω) (R₁ ω))
    hμnonneg hpointwise
  have hconstant : weightedNatAverage μ (fun _ ↦ N * (N - 1)) =
      ((N * (N - 1) : ℕ) : ℝ) := by
    unfold weightedNatAverage
    rw [← Finset.sum_mul, hμsum]
    simp
  rw [hconstant] at havg
  simpa only [weightedNatAverage, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc] using havg

end RobustPairedQuotient
end GroupApproximation
