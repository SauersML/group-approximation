import GroupApproximation.Sofic.IntegralLinearResiduallyFinite
import Mathlib.GroupTheory.CoprodI
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Free products of sign groups are residually finite

The free product `∗_{i ∈ I} (B i → ℤ/2)` of finitely many finite sign
groups acts faithfully on the free `ℤ`-module with basis the disjoint
union of the `B i` together with one basepoint coordinate: the factor at
`i` acts by signed reflections that negate the supported coordinates and
add twice the mass sitting outside block `i`.  Faithfulness is proved by
an elementary block-sum invariant propagated along the reduced words of
`Monoid.CoprodI` — no Bass--Serre theory and no Coxeter theory: for the
image `v` of the basepoint under a nonempty reduced word with first
index `i₀`, the block sums satisfy `2 + otherSum i₀ v ≤ blockSum i₀ v`,
while every other block satisfies the reverse inequality with slack `2`.

Combined with `generalLinearGroup_int_residuallyFinite`, the free
product is residually finite.  This is the statement (M′) of
`notes/SOFICITY_TOWER_MJ_DESIGN_2026-08-15.md`, to which residual
finiteness of the literal lamp sub-amalgams reduces.
-/

namespace GroupApproximation
namespace FreeProductSignReflection

open Monoid Finset
open scoped symmDiff

set_option linter.unusedSectionVars true

variable {I : Type} [DecidableEq I] [Fintype I]
variable {B : I → Type} [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)]

/-- The sign group at index `i`: functions from `B i` to `ℤ/2`, written
multiplicatively so that `Monoid.CoprodI` applies directly. -/
abbrev SignGroup (B : I → Type) (i : I) : Type :=
  B i → Multiplicative (ZMod 2)

/-- The coordinate type: the disjoint union of the blocks together with a
basepoint. -/
abbrev Coord (B : I → Type) : Type :=
  Option ((i : I) × B i)

/-- The module the free product acts on. -/
abbrev V (B : I → Type) : Type :=
  Coord B → ℤ

/-- The basepoint vector. -/
def basepoint : V B := fun x => if x = none then 1 else 0

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
@[simp] theorem basepoint_none : (basepoint : V B) none = 1 := rfl

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
@[simp]
theorem basepoint_some (p : (i : I) × B i) :
    (basepoint : V B) (some p) = 0 := rfl

/-- The set of coordinates belonging to block `i`. -/
def blockSet (i : I) : Finset (Coord B) :=
  (univ : Finset (B i)).image fun b => some ⟨i, b⟩

omit [Fintype I] in
theorem mem_blockSet_iff {i : I} {x : Coord B} :
    x ∈ blockSet i ↔ ∃ b : B i, x = some ⟨i, b⟩ := by
  constructor
  · intro hx
    rw [blockSet, mem_image] at hx
    obtain ⟨b, _, rfl⟩ := hx
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact mem_image.mpr ⟨b, mem_univ b, rfl⟩

omit [Fintype I] in
theorem none_notMem_blockSet (i : I) : (none : Coord B) ∉ blockSet i := by
  intro h
  obtain ⟨b, hb⟩ := mem_blockSet_iff.mp h
  exact Option.some_ne_none _ hb.symm

omit [Fintype I] in
theorem blockSet_disjoint {i j : I} (hij : i ≠ j) :
    Disjoint (blockSet (B := B) i) (blockSet j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  obtain ⟨b, rfl⟩ := mem_blockSet_iff.mp hxi
  obtain ⟨b', hb'⟩ := mem_blockSet_iff.mp hxj
  exact hij (congrArg Sigma.fst (Option.some_injective _ hb'))

/-- The support of a sign vector, as a set of coordinates in its block. -/
def suppSet (i : I) (g : SignGroup B i) : Finset (Coord B) :=
  ((univ : Finset (B i)).filter fun b =>
    Multiplicative.toAdd (g b) = 1).image fun b => some ⟨i, b⟩

omit [Fintype I] in
theorem suppSet_subset_blockSet (i : I) (g : SignGroup B i) :
    suppSet i g ⊆ blockSet i := by
  intro x hx
  rw [suppSet, mem_image] at hx
  obtain ⟨b, _, rfl⟩ := hx
  exact mem_blockSet_iff.mpr ⟨b, rfl⟩

omit [Fintype I] in
theorem some_mk_mem_suppSet_iff {i : I} {g : SignGroup B i} {b : B i} :
    (some ⟨i, b⟩ : Coord B) ∈ suppSet i g ↔
      Multiplicative.toAdd (g b) = 1 := by
  rw [suppSet, mem_image]
  constructor
  · rintro ⟨b', hb', heq⟩
    obtain rfl : b' = b :=
      sigma_mk_injective (Option.some_injective _ heq)
    exact (mem_filter.mp hb').2
  · exact fun hb => ⟨b, mem_filter.mpr ⟨mem_univ b, hb⟩, rfl⟩

omit [Fintype I] in
theorem suppSet_one (i : I) : suppSet i (1 : SignGroup B i) = ∅ := by
  rw [suppSet, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro b _
  simp only [Pi.one_apply, toAdd_one]
  decide

omit [Fintype I] in
theorem suppSet_nonempty_of_ne_one {i : I} {g : SignGroup B i}
    (hg : g ≠ 1) : (suppSet i g).Nonempty := by
  have hb : ∃ b : B i, g b ≠ 1 := by
    by_contra h
    apply hg
    funext b
    by_contra hb
    exact h ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hb
  refine ⟨some ⟨i, b⟩, some_mk_mem_suppSet_iff.mpr ?_⟩
  revert hb
  generalize g b = a
  revert a
  decide

omit [Fintype I] in
theorem suppSet_mul (i : I) (g h : SignGroup B i) :
    suppSet i (g * h) = suppSet i g ∆ suppSet i h := by
  have hxor : ∀ a b : ZMod 2, a + b = 1 ↔
      ((a = 1 ∧ ¬b = 1) ∨ (¬a = 1 ∧ b = 1)) := by decide
  ext x
  by_cases hx : x ∈ blockSet (B := B) i
  · obtain ⟨b, rfl⟩ := mem_blockSet_iff.mp hx
    rw [Finset.mem_symmDiff, some_mk_mem_suppSet_iff,
      some_mk_mem_suppSet_iff, some_mk_mem_suppSet_iff]
    have : Multiplicative.toAdd ((g * h) b)
        = Multiplicative.toAdd (g b) + Multiplicative.toAdd (h b) := rfl
    rw [this, hxor]
    tauto
  · constructor
    · intro hmem
      exact absurd (suppSet_subset_blockSet i (g * h) hmem) hx
    · intro hmem
      rcases Finset.mem_symmDiff.mp hmem with ⟨hmem', _⟩ | ⟨hmem', _⟩
      · exact absurd (suppSet_subset_blockSet i g hmem') hx
      · exact absurd (suppSet_subset_blockSet i h hmem') hx

/-! ## Block sums -/

/-- The sum of the coordinates of `v` over block `i`. -/
def blockSum (i : I) (v : V B) : ℤ :=
  ∑ x ∈ blockSet (B := B) i, v x

/-- The sum of the coordinates of `v` over the blocks other than `i`;
the basepoint coordinate is not included. -/
def otherSum (i : I) (v : V B) : ℤ :=
  ∑ j ∈ (univ : Finset I).erase i, blockSum j v

omit [Fintype I] in
theorem blockSum_add (i : I) (v w : V B) :
    blockSum i (v + w) = blockSum i v + blockSum i w := by
  unfold blockSum
  simp [Finset.sum_add_distrib]

theorem otherSum_add (i : I) (v w : V B) :
    otherSum i (v + w) = otherSum i v + otherSum i w := by
  unfold otherSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => blockSum_add j v w

omit [Fintype I] in
theorem blockSum_smul (i : I) (c : ℤ) (v : V B) :
    blockSum i (c • v) = c * blockSum i v := by
  unfold blockSum
  simp [Finset.mul_sum]

theorem otherSum_smul (i : I) (c : ℤ) (v : V B) :
    otherSum i (c • v) = c * otherSum i v := by
  unfold otherSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => blockSum_smul j c v

omit [Fintype I] in
theorem blockSum_basepoint (i : I) : blockSum i (basepoint : V B) = 0 := by
  unfold blockSum
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨b, rfl⟩ := mem_blockSet_iff.mp hx
  rfl

theorem otherSum_basepoint (i : I) : otherSum i (basepoint : V B) = 0 := by
  unfold otherSum
  exact Finset.sum_eq_zero fun j _ => blockSum_basepoint j

/-- Splitting `otherSum i` at a block `j ≠ i`: the rest of the sum. -/
def restSum (i j : I) (v : V B) : ℤ :=
  ∑ k ∈ ((univ : Finset I).erase i).erase j, blockSum k v

theorem otherSum_eq_blockSum_add_restSum {i j : I} (hij : j ≠ i)
    (v : V B) : otherSum i v = blockSum j v + restSum i j v := by
  unfold otherSum restSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij, mem_univ j⟩)]

theorem restSum_comm (i j : I) (v : V B) :
    restSum i j v = restSum j i v := by
  unfold restSum
  rw [Finset.erase_right_comm]

/-! ## The reflections -/

/-- The signed-reflection action of a support set inside block `i`: the
supported coordinates are replaced by twice the outside mass minus
themselves, and every other coordinate is fixed.  The outside mass is
the basepoint value plus the mass of the other blocks. -/
def reflFun (i : I) (s : Finset (Coord B)) (v : V B) : V B := fun x =>
  if x ∈ s then 2 * (v none + otherSum i v) - v x else v x

theorem reflFun_apply_notMem {i : I} {s : Finset (Coord B)} {v : V B}
    {x : Coord B} (hx : x ∉ s) : reflFun i s v x = v x := if_neg hx

theorem reflFun_apply_mem {i : I} {s : Finset (Coord B)} {v : V B}
    {x : Coord B} (hx : x ∈ s) :
    reflFun i s v x = 2 * (v none + otherSum i v) - v x := if_pos hx

theorem reflFun_none {i : I} {s : Finset (Coord B)}
    (hs : s ⊆ blockSet i) (v : V B) :
    reflFun i s v none = v none :=
  reflFun_apply_notMem fun h => none_notMem_blockSet i (hs h)

theorem reflFun_apply_of_notMem_blockSet {i : I} {s : Finset (Coord B)}
    (hs : s ⊆ blockSet i) {v : V B} {x : Coord B}
    (hx : x ∉ blockSet i) : reflFun i s v x = v x :=
  reflFun_apply_notMem fun h => hx (hs h)

theorem blockSum_reflFun_of_ne {i j : I} (hij : j ≠ i)
    {s : Finset (Coord B)} (hs : s ⊆ blockSet i) (v : V B) :
    blockSum j (reflFun i s v) = blockSum j v := by
  unfold blockSum
  refine Finset.sum_congr rfl fun x hx => ?_
  refine reflFun_apply_of_notMem_blockSet hs fun hxi => ?_
  exact (Finset.disjoint_left.mp (blockSet_disjoint hij)) hx hxi

theorem otherSum_reflFun {i : I} {s : Finset (Coord B)}
    (hs : s ⊆ blockSet i) (v : V B) :
    otherSum i (reflFun i s v) = otherSum i v := by
  unfold otherSum
  exact Finset.sum_congr rfl fun j hj =>
    blockSum_reflFun_of_ne (Finset.ne_of_mem_erase hj) hs v

theorem reflFun_reflFun {i : I} {s : Finset (Coord B)}
    (hs : s ⊆ blockSet i) (v : V B) :
    reflFun i s (reflFun i s v) = v := by
  funext x
  by_cases hx : x ∈ s
  · rw [reflFun_apply_mem hx, reflFun_none hs, otherSum_reflFun hs,
      reflFun_apply_mem hx]
    ring
  · rw [reflFun_apply_notMem hx, reflFun_apply_notMem hx]

theorem reflFun_add (i : I) (s : Finset (Coord B)) (v w : V B) :
    reflFun i s (v + w) = reflFun i s v + reflFun i s w := by
  funext x
  by_cases hx : x ∈ s
  · simp only [reflFun, hx, if_true, Pi.add_apply, otherSum_add]
    ring
  · simp [reflFun, hx]

theorem reflFun_smul (i : I) (s : Finset (Coord B)) (c : ℤ) (v : V B) :
    reflFun i s (c • v) = c • reflFun i s v := by
  funext x
  by_cases hx : x ∈ s
  · simp only [reflFun, hx, if_true, Pi.smul_apply, smul_eq_mul,
      otherSum_smul]
    ring
  · simp [reflFun, hx]

/-- Reflections in the same block compose by symmetric difference of
their supports. -/
theorem reflFun_reflFun_symmDiff {i : I} {s t : Finset (Coord B)}
    (_hs : s ⊆ blockSet i) (ht : t ⊆ blockSet i) (v : V B) :
    reflFun i s (reflFun i t v) = reflFun i (s ∆ t) v := by
  funext x
  have houter : reflFun i t v none + otherSum i (reflFun i t v)
      = v none + otherSum i v := by
    rw [reflFun_none ht, otherSum_reflFun ht]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t
  · rw [reflFun_apply_mem hxs, houter, reflFun_apply_mem hxt,
      reflFun_apply_notMem (by simp [Finset.mem_symmDiff, hxs, hxt])]
    ring
  · rw [reflFun_apply_mem hxs, houter, reflFun_apply_notMem hxt,
      reflFun_apply_mem (by simp [Finset.mem_symmDiff, hxs, hxt])]
  · rw [reflFun_apply_notMem hxs, reflFun_apply_mem hxt,
      reflFun_apply_mem (by simp [Finset.mem_symmDiff, hxs, hxt])]
  · rw [reflFun_apply_notMem hxs, reflFun_apply_notMem hxt,
      reflFun_apply_notMem (by simp [Finset.mem_symmDiff, hxs, hxt])]

/-- The reflection at a support set inside block `i`, as a linear
automorphism. -/
def reflEquiv (i : I) (s : Finset (Coord B)) (hs : s ⊆ blockSet i) :
    V B ≃ₗ[ℤ] V B where
  toFun := reflFun i s
  map_add' := reflFun_add i s
  map_smul' := reflFun_smul i s
  invFun := reflFun i s
  left_inv := reflFun_reflFun hs
  right_inv := reflFun_reflFun hs

@[simp] theorem reflEquiv_apply (i : I) (s : Finset (Coord B))
    (hs : s ⊆ blockSet i) (v : V B) :
    reflEquiv i s hs v = reflFun i s v := rfl

/-- The factor homomorphism: a sign vector acts by the reflection at its
support. -/
def signHom (i : I) : SignGroup B i →* (V B ≃ₗ[ℤ] V B) where
  toFun g := reflEquiv i (suppSet i g) (suppSet_subset_blockSet i g)
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    show reflFun i (suppSet i (1 : SignGroup B i)) v = v
    rw [suppSet_one]
    funext x
    exact reflFun_apply_notMem (Finset.notMem_empty x)
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    show reflFun i (suppSet i (g * h)) v = _
    rw [suppSet_mul]
    rw [← reflFun_reflFun_symmDiff (suppSet_subset_blockSet i g)
      (suppSet_subset_blockSet i h)]
    rfl

/-- The representation of the free product. -/
def rho : CoprodI (SignGroup B) →* (V B ≃ₗ[ℤ] V B) :=
  CoprodI.lift signHom

/-! ## The invariant -/

/-- The invariant carried along a reduced word whose first index is
`i₀`. -/
def GoodAt (i₀ : I) (v : V B) : Prop :=
  v none = 1 ∧ (∀ x, 0 ≤ v x) ∧
    2 + otherSum i₀ v ≤ blockSum i₀ v ∧
    ∀ j, j ≠ i₀ → blockSum j v + 2 ≤ otherSum j v

omit [Fintype I] in
theorem single_le_blockSum {i : I} {v : V B} (hv : ∀ x, 0 ≤ v x)
    {b : B i} : v (some ⟨i, b⟩) ≤ blockSum i v :=
  Finset.single_le_sum (fun x _ => hv x) (mem_blockSet_iff.mpr ⟨b, rfl⟩)

omit [Fintype I] in
theorem blockSum_nonneg {i : I} {v : V B} (hv : ∀ x, 0 ≤ v x) :
    0 ≤ blockSum i v :=
  Finset.sum_nonneg fun x _ => hv x

theorem restSum_nonneg {i j : I} {v : V B} (hv : ∀ x, 0 ≤ v x) :
    0 ≤ restSum i j v :=
  Finset.sum_nonneg fun _ _ => blockSum_nonneg hv

/-- The block sum of a reflected vector, in closed form. -/
theorem blockSum_reflFun_self {i : I} {s : Finset (Coord B)}
    (hs : s ⊆ blockSet i) (v : V B) :
    blockSum i (reflFun i s v)
      = blockSum i v
        + ((s.card : ℤ) * (2 * (v none + otherSum i v))
          - 2 * ∑ x ∈ s, v x) := by
  unfold blockSum
  have hsplit : ∀ x ∈ blockSet (B := B) i,
      reflFun i s v x
        = v x + (if x ∈ s then 2 * (v none + otherSum i v) - 2 * v x
            else 0) := by
    intro x _
    by_cases hx : x ∈ s
    · rw [reflFun_apply_mem hx, if_pos hx]
      ring
    · rw [reflFun_apply_notMem hx, if_neg hx]
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hs,
    Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
  ring

/-- Propagation of the invariant: applying a nontrivial reflection in a
different block moves the invariant to the new block. -/
theorem goodAt_reflFun {i i₀ : I} (hne : i ≠ i₀) {g : SignGroup B i}
    (hg : g ≠ 1) {v : V B} (hv : GoodAt i₀ v) :
    GoodAt i (reflFun i (suppSet i g) v) := by
  obtain ⟨hnone, hpos, hfirst, hrest⟩ := hv
  set s := suppSet i g with hsdef
  have hs : s ⊆ blockSet i := suppSet_subset_blockSet i g
  have hcard : 1 ≤ (s.card : ℤ) := by
    have := Finset.card_pos.mpr (suppSet_nonempty_of_ne_one hg)
    exact_mod_cast this
  set v' := reflFun i s v with hv'def
  -- unchanged data
  have hnone' : v' none = v none := reflFun_none hs v
  have hother' : otherSum i v' = otherSum i v := otherSum_reflFun hs v
  have hblock' : ∀ j, j ≠ i → blockSum j v' = blockSum j v := fun j hj =>
    blockSum_reflFun_of_ne hj hs v
  -- the i-block inequality of `v`, from the invariant at `i ≠ i₀`
  have hislack : blockSum i v + 2 ≤ otherSum i v := hrest i hne
  -- partial-sum bound
  have hsub : ∑ x ∈ s, v x ≤ blockSum i v := by
    unfold blockSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hs fun x _ _ => hpos x
  have hsubpos : 0 ≤ ∑ x ∈ s, v x :=
    Finset.sum_nonneg fun x _ => hpos x
  -- closed form of the new i-block sum
  have hself := blockSum_reflFun_self hs v
  rw [hnone] at hself
  -- nonnegativity of the reflected coordinates
  have hpos' : ∀ x, 0 ≤ v' x := by
    intro x
    by_cases hx : x ∈ s
    · rw [hv'def, reflFun_apply_mem hx, hnone]
      have hxle : v x ≤ blockSum i v := by
        obtain ⟨b, rfl⟩ := mem_blockSet_iff.mp (hs hx)
        exact single_le_blockSum hpos
      linarith [blockSum_nonneg (i := i) hpos, hislack]
    · rw [hv'def, reflFun_apply_notMem hx]
      exact hpos x
  -- growth of the i-block sum
  have hosnn : 0 ≤ otherSum i v :=
    Finset.sum_nonneg fun j _ => blockSum_nonneg hpos
  have hprod : 2 * (1 + otherSum i v)
      ≤ (s.card : ℤ) * (2 * (1 + otherSum i v)) :=
    le_mul_of_one_le_left (by linarith) hcard
  have hgrow : blockSum i v + (2 + 2 * otherSum i v - 2 * blockSum i v)
      ≤ blockSum i v' := by
    rw [hself]
    linarith [hsub, hsubpos, hprod]
  refine ⟨by rw [hnone', hnone], hpos', ?_, ?_⟩
  · -- the new first-block inequality
    rw [hother']
    linarith [hgrow, hislack]
  · -- the reverse inequality at every other block
    intro j hj
    by_cases hji₀ : j = i₀
    · subst hji₀
      have hsplitv : otherSum i v = blockSum j v + restSum i j v :=
        otherSum_eq_blockSum_add_restSum (fun h => hne h.symm) v
      have hsplitv' : otherSum j v' = blockSum i v' + restSum j i v' :=
        otherSum_eq_blockSum_add_restSum (Ne.symm hj) v'
      have hsplitvj : otherSum j v = blockSum i v + restSum j i v :=
        otherSum_eq_blockSum_add_restSum (Ne.symm hj) v
      have hrestsame : restSum j i v' = restSum j i v := by
        unfold restSum
        refine Finset.sum_congr rfl fun k hk => ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        exact hblock' k hki
      have hbj' : blockSum j v' = blockSum j v := hblock' j hj
      -- target: blockSum j v' + 2 ≤ otherSum j v'
      rw [hbj', hsplitv', hrestsame]
      have hrs : restSum j i v = restSum i j v := restSum_comm j i v
      have hrnn : 0 ≤ restSum i j v :=
        restSum_nonneg (i := i) (j := j) hpos
      rw [hrs]
      -- goal: blockSum j v + 2 ≤ blockSum i v' + restSum i j v
      linarith [hgrow, hsplitv, hislack, hrnn]
    · have hbj' : blockSum j v' = blockSum j v := hblock' j hj
      have hsplitv' : otherSum j v'
          = blockSum i v' + restSum j i v' :=
        otherSum_eq_blockSum_add_restSum (Ne.symm hj) v'
      have hsplitvj : otherSum j v = blockSum i v + restSum j i v :=
        otherSum_eq_blockSum_add_restSum (Ne.symm hj) v
      have hrestsame : restSum j i v' = restSum j i v := by
        unfold restSum
        refine Finset.sum_congr rfl fun k hk => ?_
        exact hblock' k (Finset.ne_of_mem_erase hk)
      have hgrow' : blockSum i v ≤ blockSum i v' := by
        linarith [hgrow, hislack]
      rw [hbj', hsplitv', hrestsame]
      have hjrest := hrest j hji₀
      rw [hsplitvj] at hjrest
      linarith [hgrow']

/-- The base case: one nontrivial reflection applied to the basepoint. -/
theorem goodAt_basepoint {i : I} {g : SignGroup B i} (hg : g ≠ 1) :
    GoodAt i (reflFun i (suppSet i g) basepoint) := by
  set s := suppSet i g with hsdef
  have hs : s ⊆ blockSet i := suppSet_subset_blockSet i g
  have hcard : 1 ≤ (s.card : ℤ) := by
    have := Finset.card_pos.mpr (suppSet_nonempty_of_ne_one hg)
    exact_mod_cast this
  set v' := reflFun i s (basepoint : V B) with hv'def
  have hnone' : v' none = 1 := by
    rw [hv'def, reflFun_none hs, basepoint_none]
  have happly : ∀ x, v' x = if x ∈ s then 2 else basepoint x := by
    intro x
    by_cases hx : x ∈ s
    · rw [hv'def, reflFun_apply_mem hx, basepoint_none,
        otherSum_basepoint, if_pos hx]
      obtain ⟨b, rfl⟩ := mem_blockSet_iff.mp (hs hx)
      rw [basepoint_some]
      ring
    · rw [hv'def, reflFun_apply_notMem hx, if_neg hx]
  have hpos' : ∀ x, 0 ≤ v' x := by
    intro x
    rw [happly x]
    by_cases hx : x ∈ s
    · rw [if_pos hx]; norm_num
    · rw [if_neg hx]
      unfold basepoint
      by_cases hxn : x = none <;> simp [hxn]
  have hblocki : blockSum i v' = 2 * s.card := by
    rw [hv'def, blockSum_reflFun_self hs, basepoint_none,
      otherSum_basepoint, blockSum_basepoint]
    have hzero : ∑ x ∈ s, (basepoint : V B) x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      obtain ⟨b, rfl⟩ := mem_blockSet_iff.mp (hs hx)
      rfl
    rw [hzero]
    ring
  have hother' : otherSum i v' = 0 := by
    rw [hv'def, otherSum_reflFun hs, otherSum_basepoint]
  have hblockj : ∀ j, j ≠ i → blockSum j v' = 0 := by
    intro j hj
    rw [hv'def, blockSum_reflFun_of_ne hj hs, blockSum_basepoint]
  refine ⟨hnone', hpos', ?_, ?_⟩
  · rw [hother', hblocki]
    linarith
  · intro j hj
    rw [hblockj j hj,
      otherSum_eq_blockSum_add_restSum (fun h => hj h.symm) v', hblocki]
    have := restSum_nonneg (i := j) (j := i) hpos'
    linarith

/-! ## The word induction and injectivity -/

/-- The image of a list of letters, as a product of reflections. -/
def listProd (L : List ((i : I) × SignGroup B i)) : V B ≃ₗ[ℤ] V B :=
  (L.map fun p => signHom p.1 p.2).prod

@[simp] theorem listProd_nil :
    listProd (B := B) [] = 1 := by
  simp [listProd]

theorem listProd_cons (p : (i : I) × SignGroup B i)
    (L : List ((i : I) × SignGroup B i)) :
    listProd (p :: L) = signHom p.1 p.2 * listProd L := by
  simp [listProd]

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
@[simp]
theorem mul_linearEquiv_apply (e f : V B ≃ₗ[ℤ] V B) (v : V B) :
    (e * f) v = e (f v) := rfl

theorem goodAt_listProd :
    ∀ (L : List ((i : I) × SignGroup B i)),
      (∀ p ∈ L, p.2 ≠ 1) →
      L.IsChain (fun p q => p.1 ≠ q.1) →
      ∀ (hL : L ≠ []),
      GoodAt (L.head hL).1 (listProd L basepoint) := by
  intro L
  induction L with
  | nil => intro _ _ hL; exact absurd rfl hL
  | cons p L ih =>
    intro hone hchain _
    match L, hchain with
    | [], _ =>
      rw [listProd_cons, listProd_nil, mul_linearEquiv_apply]
      show GoodAt p.1 (reflFun p.1 (suppSet p.1 p.2) ((1 : V B ≃ₗ[ℤ] V B) basepoint))
      exact goodAt_basepoint (hone p (List.mem_cons_self ..))
    | q :: L', hchain =>
      have hpq : p.1 ≠ q.1 := by
        cases hchain with
        | cons_cons h _ => exact h
      have hchain' : (q :: L').IsChain (fun p q => p.1 ≠ q.1) := by
        cases hchain with
        | cons_cons _ h => exact h
      have hone' : ∀ r ∈ q :: L', r.2 ≠ 1 := fun r hr =>
        hone r (List.mem_cons_of_mem p hr)
      have hprev := ih hone' hchain' (List.cons_ne_nil q L')
      rw [listProd_cons, mul_linearEquiv_apply]
      show GoodAt p.1
        (reflFun p.1 (suppSet p.1 p.2) (listProd (q :: L') basepoint))
      exact goodAt_reflFun hpq (hone p (List.mem_cons_self ..)) hprev

/-- **Faithfulness of the signed-reflection representation.** -/
theorem rho_injective :
    Function.Injective (rho (B := B)) := by
  rw [injective_iff_map_eq_one]
  intro g hgone
  by_contra hg
  set w := CoprodI.Word.equiv g with hwdef
  have hprod : w.prod = g := CoprodI.Word.equiv.symm_apply_apply g
  have hlist : w.toList ≠ [] := by
    intro hempty
    apply hg
    have hwempty : w = CoprodI.Word.empty := by
      apply CoprodI.Word.ext
      exact hempty
    rw [← hprod, hwempty, CoprodI.Word.prod_empty]
  have hrho : rho g = listProd w.toList := by
    rw [← hprod]
    unfold rho listProd
    show (CoprodI.lift signHom)
        (List.prod (w.toList.map fun l => CoprodI.of l.snd)) = _
    rw [map_list_prod, List.map_map]
    have hfun : (⇑(CoprodI.lift signHom) ∘ fun l : (i : I) × SignGroup B i =>
        CoprodI.of l.snd) = fun p => signHom p.1 p.2 := by
      funext l
      exact CoprodI.lift_of ..
    rw [hfun]
  have hgood := goodAt_listProd w.toList
    (fun p hp => w.ne_one p hp) w.chain_ne hlist
  rw [← hrho] at hgood
  rw [hgone] at hgood
  obtain ⟨_, _, hfirst, _⟩ := hgood
  have h1 : (1 : V B ≃ₗ[ℤ] V B) basepoint = basepoint := rfl
  rw [h1, blockSum_basepoint, otherSum_basepoint] at hfirst
  norm_num at hfirst

/-! ## Residual finiteness -/

/-- The free product of finitely many finite sign groups embeds in the
integral general linear group of its coordinate module. -/
noncomputable def toGL :
    CoprodI (SignGroup B) →* Matrix.GeneralLinearGroup (Coord B) ℤ :=
  (Units.mapEquiv
      (LinearMap.toMatrixAlgEquiv'
        (R := ℤ) (n := Coord B)).toRingEquiv.toMulEquiv).toMonoidHom.comp
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ
        (V B)).symm.toMonoidHom).comp (rho (B := B)))

theorem toGL_injective : Function.Injective (toGL (B := B)) := by
  unfold toGL
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (MulEquiv.injective _).comp
    ((MulEquiv.injective _).comp rho_injective)

/-- **Free products of finitely many finite sign groups are residually
finite** — the statement (M′) of the soficity-tower design note. -/
theorem residuallyFinite_coprodI_signGroup :
    Group.ResiduallyFinite (CoprodI (SignGroup B)) := by
  haveI := generalLinearGroup_int_residuallyFinite (Coord B)
  exact residuallyFinite_of_injective toGL toGL_injective

end FreeProductSignReflection
end GroupApproximation
