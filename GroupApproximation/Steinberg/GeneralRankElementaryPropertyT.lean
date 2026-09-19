import GroupApproximation.PropertyT.A2MagicHilbert
import GroupApproximation.Steinberg.HigherRankFiniteControl
import Mathlib.RingTheory.FiniteType

/-!
# Rectangular block roots and property `(T)` in every elementary rank

The Ershov--Jaikin-Zapirain magic-graph theorem
(`A2MagicHilbert.exists_rootSet_isKazhdan`) applies to any strongly graded
`A₂` root system in an abstract group whose root subgroups have one common
positive exponent.  The tree instantiates it in rank three
(`elementaryA2System`) and, for the Steinberg group, at higher rank
(`SteinbergBlockRoot.blockA2System`) -- but the latter is built from a
`CompleteMatrixFamily R κ`, i.e. a full set of matrix units inside `R`, which
a general ring does not have.

Inside the **elementary** group there are honest matrices, so the higher-rank
`A₂` system can be built with no such family: partition the index set into
three blocks and take the rectangular transvection subgroups `1 + M` with `M`
supported on `Bᵢ × Bⱼ`.  This file does that.

## Main results

* `BlockSupported`, `blockRootSubgroup`, `blockA2System` -- the rectangular
  block `A₂` system inside `EL_ι(R)` for an arbitrary three-block partition
  `blk : ι → Fin 3` of an arbitrary finite index type over an arbitrary ring.
  Two hypotheses are needed, and both are discharged below for `Fin n`:
  `blk` is surjective (all three blocks are nonempty), and every rectangular
  block factors through the third block.
* `blockElementaryA2System` -- the instance for `Fin n`, `3 ≤ n`, using the
  partition `{0}`, `{1}`, `{2, …, n-1}`.  With two singleton blocks the
  factorization hypothesis is automatic for every `n ≥ 3`; an equal-thirds
  partition would not satisfy it unless `3 ∣ n`.
* `blockElementary_exists_rootSet_isKazhdan` -- **the union of the six
  rectangular block roots of `EL_n(R)` is a Kazhdan subset for every `n ≥ 3`
  and every ring of positive characteristic.**  No finiteness, no finite
  generation and no matrix family: only `CharP R p` with `0 < p`.
* `finiteTypeCharTwoElementary_hasKazhdanPropertyT` -- the property-`(T)`
  conclusion that the above yields *with the finite control sets the tree
  actually has*: `EL_n(R)` has property `(T)` for every `n ≥ 3` and every
  finite-type `ZMod 2`-algebra `R`.

## What the property-`(T)` conclusion costs, and what it does not cover

`IsKazhdanSubset.to_pair_of_controls` needs a second, independent input: a
finite subset controlling displacement by the whole (infinite) root union.
The Kazhdan-subset half above is characteristic-free, but the control half is
not.  The only rank-`n` control set in the tree is
`SteinbergHigherRankFiniteControl.finiteControlSetAt`, which lives over
`FreeAlgebra (ZMod 2) X`.  Pushing it forward along the canonical surjection
`St_n(R) ↠ EL_n(R)` (`SteinbergGroup.projection`) gives
`elementaryControlSet_controls_rootSet`, and hence property `(T)` in
characteristic two only.

The parallel elementary lane `PropertyT.FiniteFieldElementaryPropertyT`
proves rank three over *every* finite field, but its control estimate
(`FiniteFieldElementaryPropertyT.controlSet_controls_rootSet`) is stated for
`elementaryA2System` at `Fin 3`, and there is no homomorphism
`EL₃(A) →* EL_n(A)` in the tree to transport it along:
`elementaryReindexEquiv` needs an equivalence of index types, not an
embedding.  Producing that identity-padding homomorphism is exactly what is
missing to upgrade `finiteTypeCharTwoElementary_hasKazhdanPropertyT` to all
finite fields; it is formalization work, not new mathematics.  Nothing here
touches the characteristic-zero (base-ring) axis of the
Ershov--Jaikin-Zapirain theorem.
-/

namespace GroupApproximation
namespace BlockElementary

open scoped commutatorElement

/-! ### Block support -/

section Support

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- `M` is supported in the rectangular block `Bᵢ × Bⱼ` of the three-block
decomposition `blk`. -/
def BlockSupported (blk : ι → Fin 3) (i j : Fin 3) (M : Matrix ι ι R) : Prop :=
  ∀ a b : ι, M a b ≠ 0 → blk a = i ∧ blk b = j

omit [Fintype ι] [DecidableEq ι] in
theorem BlockSupported.row {blk : ι → Fin 3} {i j : Fin 3} {M : Matrix ι ι R}
    (hM : BlockSupported blk i j M) {a b : ι} (ha : blk a ≠ i) : M a b = 0 := by
  by_contra hne
  exact ha (hM a b hne).1

omit [Fintype ι] [DecidableEq ι] in
theorem BlockSupported.col {blk : ι → Fin 3} {i j : Fin 3} {M : Matrix ι ι R}
    (hM : BlockSupported blk i j M) {a b : ι} (hb : blk b ≠ j) : M a b = 0 := by
  by_contra hne
  exact hb (hM a b hne).2

omit [Fintype ι] [DecidableEq ι] in
theorem blockSupported_zero (blk : ι → Fin 3) (i j : Fin 3) :
    BlockSupported (R := R) blk i j 0 := by
  intro a b hab
  exact absurd (Matrix.zero_apply a b) hab

omit [Fintype ι] [DecidableEq ι] in
theorem BlockSupported.add {blk : ι → Fin 3} {i j : Fin 3} {M N : Matrix ι ι R}
    (hM : BlockSupported blk i j M) (hN : BlockSupported blk i j N) :
    BlockSupported blk i j (M + N) := by
  intro a b hab
  rw [Matrix.add_apply] at hab
  by_cases hMa : M a b = 0
  · refine hN a b ?_
    intro hNa
    exact hab (by rw [hMa, hNa, add_zero])
  · exact hM a b hMa

omit [Fintype ι] [DecidableEq ι] in
theorem BlockSupported.neg {blk : ι → Fin 3} {i j : Fin 3} {M : Matrix ι ι R}
    (hM : BlockSupported blk i j M) : BlockSupported blk i j (-M) := by
  intro a b hab
  refine hM a b ?_
  intro h
  exact hab (by rw [Matrix.neg_apply, h, neg_zero])

omit [DecidableEq ι] in
/-- Two rectangular blocks whose inner indices differ multiply to zero. -/
theorem mul_eq_zero_of_blockSupported {blk : ι → Fin 3} {i j k l : Fin 3}
    {M N : Matrix ι ι R} (hM : BlockSupported blk i j M)
    (hN : BlockSupported blk k l N) (hjk : j ≠ k) : M * N = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero ?_
  intro c _
  by_cases hc : blk c = j
  · have hck : blk c ≠ k := by
      rw [hc]
      exact hjk
    rw [hN.row hck, mul_zero]
  · rw [hM.col hc, zero_mul]

omit [DecidableEq ι] in
/-- Composable rectangular blocks multiply into the composite block. -/
theorem BlockSupported.mul {blk : ι → Fin 3} {i j k : Fin 3}
    {M N : Matrix ι ι R} (hM : BlockSupported blk i j M)
    (hN : BlockSupported blk j k N) : BlockSupported blk i k (M * N) := by
  intro a b hab
  constructor
  · by_contra ha
    refine hab ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero ?_
    intro c _
    rw [hM.row ha, zero_mul]
  · by_contra hb
    refine hab ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero ?_
    intro c _
    rw [hN.col hb, mul_zero]

omit [DecidableEq ι] in
/-- A rectangular block off the block diagonal is square-zero. -/
theorem BlockSupported.mul_self {blk : ι → Fin 3} {i j : Fin 3}
    {M : Matrix ι ι R} (hij : i ≠ j) (hM : BlockSupported blk i j M) :
    M * M = 0 :=
  mul_eq_zero_of_blockSupported hM hM hij.symm

omit [Fintype ι] in
theorem blockSupported_single {blk : ι → Fin 3} {i j : Fin 3} {u v : ι}
    (hu : blk u = i) (hv : blk v = j) (c : R) :
    BlockSupported blk i j (Matrix.single u v c) := by
  intro a b hab
  by_cases h : u = a ∧ v = b
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨hu, hv⟩
  · exact absurd (Matrix.single_apply_of_ne u v c a b h) hab

end Support

/-! ### Unipotent units and their underlying matrices -/

section Unit

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The unipotent unit `1 + M` attached to a square-zero matrix. -/
def blockUnit (M : Matrix ι ι R) (hM : M * M = 0) : (Matrix ι ι R)ˣ where
  val := 1 + M
  inv := 1 - M
  val_inv := by noncomm_ring [hM]
  inv_val := by noncomm_ring [hM]

@[simp] theorem blockUnit_val (M : Matrix ι ι R) (hM : M * M = 0) :
    ((blockUnit M hM : (Matrix ι ι R)ˣ) : Matrix ι ι R) = 1 + M := rfl

/-- The underlying matrix of an element of the elementary group. -/
def mat (g : elementaryGroup ι R) : Matrix ι ι R :=
  ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R)

@[simp] theorem mat_one : mat (1 : elementaryGroup ι R) = 1 := rfl

@[simp] theorem mat_mul (g h : elementaryGroup ι R) :
    mat (g * h) = mat g * mat h := rfl

@[simp] theorem mat_elementaryRoot (u v : ι) (huv : u ≠ v) (a : R) :
    mat (elementaryRoot u v huv a) = 1 + Matrix.single u v a := rfl

theorem mat_injective : Function.Injective (mat (ι := ι) (R := R)) := by
  intro g h hgh
  exact Subtype.ext (Units.ext hgh)

@[simp] theorem mat_pow (g : elementaryGroup ι R) (m : ℕ) :
    mat (g ^ m) = mat g ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ, ih]

/-- The matrix of the inverse of a unipotent group element. -/
theorem mat_inv (g : elementaryGroup ι R) {M : Matrix ι ι R}
    (hM : M * M = 0) (hg : mat g = 1 + M) : mat g⁻¹ = 1 - M := by
  have hone : mat g⁻¹ * mat g = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
  have hval : mat g * (1 - M) = 1 := by
    rw [hg]
    noncomm_ring [hM]
  calc
    mat g⁻¹ = mat g⁻¹ * (mat g * (1 - M)) := by rw [hval, mul_one]
    _ = mat g⁻¹ * mat g * (1 - M) := by rw [mul_assoc]
    _ = 1 - M := by rw [hone, one_mul]

/-- Powers of a unipotent matrix are additive in the nilpotent part. -/
theorem one_add_pow (M : Matrix ι ι R) (hM : M * M = 0) (m : ℕ) :
    (1 + M) ^ m = 1 + m • M := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (m • M) * M = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hM, mul_zero]
      rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, h, add_zero,
        succ_nsmul]
      abel

omit [Fintype ι] [DecidableEq ι] in
theorem char_nsmul_eq_zero (p : ℕ) [CharP R p] (M : Matrix ι ι R) :
    p • M = (0 : Matrix ι ι R) := by
  ext a b
  rw [Matrix.smul_apply, Matrix.zero_apply, nsmul_eq_mul, CharP.cast_eq_zero,
    zero_mul]

/-- The restriction of `M` to a finite set of matrix positions. -/
def blockRestrict (M : Matrix ι ι R) (s : Finset (ι × ι)) : Matrix ι ι R :=
  Matrix.of fun a b => if (a, b) ∈ s then M a b else 0

omit [Fintype ι] in
theorem blockRestrict_apply (M : Matrix ι ι R) (s : Finset (ι × ι)) (a b : ι) :
    blockRestrict M s a b = if (a, b) ∈ s then M a b else 0 := rfl

omit [Fintype ι] in
@[simp] theorem blockRestrict_empty (M : Matrix ι ι R) :
    blockRestrict M ∅ = 0 := by
  ext a b
  simp [blockRestrict_apply]

@[simp] theorem blockRestrict_univ (M : Matrix ι ι R) :
    blockRestrict M Finset.univ = M := by
  ext a b
  simp [blockRestrict_apply]

omit [Fintype ι] in
/-- Restricting to an inserted matrix position splits off its single-entry
matrix. -/
theorem blockRestrict_insert (M : Matrix ι ι R) (u v : ι) (s : Finset (ι × ι))
    (hs : (u, v) ∉ s) :
    blockRestrict M (insert (u, v) s) =
      Matrix.single u v (M u v) + blockRestrict M s := by
  ext a b
  rw [Matrix.add_apply, blockRestrict_apply, blockRestrict_apply]
  by_cases hab : u = a ∧ v = b
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.single_apply_same, if_pos (Finset.mem_insert_self (u, v) s),
      if_neg hs, add_zero]
  · rw [Matrix.single_apply_of_ne u v (M u v) a b hab, zero_add]
    have hmem : ((a, b) ∈ insert (u, v) s) ↔ ((a, b) ∈ s) := by
      rw [Finset.mem_insert]
      constructor
      · rintro (h | h)
        · simp only [Prod.mk.injEq] at h
          exact absurd ⟨h.1.symm, h.2.symm⟩ hab
        · exact h
      · exact Or.inr
    by_cases hin : (a, b) ∈ s
    · rw [if_pos (hmem.mpr hin), if_pos hin]
    · rw [if_neg (fun h => hin (hmem.mp h)), if_neg hin]

omit [Fintype ι] in
/-- Restriction preserves rectangular block support. -/
theorem blockRestrict_blockSupported {blk : ι → Fin 3} {i j : Fin 3}
    {M : Matrix ι ι R} (hM : BlockSupported blk i j M) (s : Finset (ι × ι)) :
    BlockSupported blk i j (blockRestrict M s) := by
  intro a b hab
  rw [blockRestrict_apply] at hab
  by_cases hs : (a, b) ∈ s
  · rw [if_pos hs] at hab
    exact hM a b hab
  · rw [if_neg hs] at hab
    exact absurd rfl hab

end Unit

/-! ### Rectangular blocks lie in the elementary group -/

section Membership

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

private theorem mem_elementaryGroup_of_blockRestrict {blk : ι → Fin 3}
    {i j : Fin 3} {M : Matrix ι ι R} (hij : i ≠ j)
    (hM : BlockSupported blk i j M) :
    ∀ (s : Finset (ι × ι)) (g : (Matrix ι ι R)ˣ),
      (g : Matrix ι ι R) = 1 + blockRestrict M s → g ∈ elementaryGroup ι R := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro g hg
      have hg1 : g = 1 := Units.ext (by simp [hg])
      rw [hg1]
      exact one_mem _
  | insert p s hs ih =>
      obtain ⟨u, v⟩ := p
      intro g hg
      by_cases hc : M u v = 0
      · refine ih g ?_
        rw [hg, blockRestrict_insert M u v s hs, hc, Matrix.single_zero,
          zero_add]
      · have hbu : blk u = i := (hM u v hc).1
        have hbv : blk v = j := (hM u v hc).2
        have huv : u ≠ v := by
          intro h
          refine hij ?_
          rw [← hbu, ← hbv, h]
        have hNsupp : BlockSupported blk i j (blockRestrict M s) :=
          blockRestrict_blockSupported hM s
        have hNN : blockRestrict M s * blockRestrict M s = 0 :=
          BlockSupported.mul_self hij hNsupp
        have hwmem : blockUnit (blockRestrict M s) hNN ∈ elementaryGroup ι R :=
          ih _ (blockUnit_val _ hNN)
        have hz0 : Matrix.single u v (M u v) * blockRestrict M s = 0 :=
          mul_eq_zero_of_blockSupported (blockSupported_single hbu hbv _)
            hNsupp hij.symm
        have hgw : g = elementaryUnit u v huv (M u v) *
            blockUnit (blockRestrict M s) hNN := by
          refine Units.ext ?_
          rw [hg, Units.val_mul, blockRestrict_insert M u v s hs]
          show 1 + (Matrix.single u v (M u v) + blockRestrict M s) =
            (1 + Matrix.single u v (M u v)) * (1 + blockRestrict M s)
          noncomm_ring [hz0]
        rw [hgw]
        exact mul_mem (elementaryUnit_mem _ _ _ _) hwmem

/-- Every rectangular block unipotent is an element of the elementary group.
This is what makes the rectangular root subgroups honest subgroups of
`EL_ι(R)`. -/
theorem blockUnit_mem_elementaryGroup {blk : ι → Fin 3} {i j : Fin 3}
    {M : Matrix ι ι R} (hij : i ≠ j) (hM : BlockSupported blk i j M) :
    blockUnit M (BlockSupported.mul_self hij hM) ∈ elementaryGroup ι R :=
  mem_elementaryGroup_of_blockRestrict hij hM Finset.univ _ (by simp)

/-- The element of `EL_ι(R)` attached to a rectangular block matrix. -/
def blockElement (blk : ι → Fin 3) (i j : Fin 3) (hij : i ≠ j)
    (M : Matrix ι ι R) (hM : BlockSupported blk i j M) : elementaryGroup ι R :=
  ⟨blockUnit M (BlockSupported.mul_self hij hM),
    blockUnit_mem_elementaryGroup hij hM⟩

@[simp] theorem mat_blockElement (blk : ι → Fin 3) (i j : Fin 3) (hij : i ≠ j)
    (M : Matrix ι ι R) (hM : BlockSupported blk i j M) :
    mat (blockElement blk i j hij M hM) = 1 + M := rfl

end Membership

/-! ### The rectangular block `A₂` system -/

section Roots

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The rectangular root subgroup of `EL_ι(R)` attached to the ordered pair
of blocks `(i, j)`. -/
def blockRootSubgroup (blk : ι → Fin 3) (i j : Fin 3) (hij : i ≠ j) :
    Subgroup (elementaryGroup ι R) where
  carrier := {g | ∃ M : Matrix ι ι R, BlockSupported blk i j M ∧ mat g = 1 + M}
  one_mem' := ⟨0, blockSupported_zero blk i j, by simp⟩
  mul_mem' := by
    rintro x y ⟨M, hM, hx⟩ ⟨N, hN, hy⟩
    refine ⟨M + N, hM.add hN, ?_⟩
    have hz : M * N = 0 := mul_eq_zero_of_blockSupported hM hN hij.symm
    rw [mat_mul, hx, hy]
    noncomm_ring [hz]
  inv_mem' := by
    rintro x ⟨M, hM, hx⟩
    refine ⟨-M, hM.neg, ?_⟩
    rw [mat_inv x (BlockSupported.mul_self hij hM) hx, sub_eq_add_neg]

theorem mem_blockRootSubgroup_iff (blk : ι → Fin 3) (i j : Fin 3) (hij : i ≠ j)
    (g : elementaryGroup ι R) :
    g ∈ blockRootSubgroup blk i j hij ↔
      ∃ M : Matrix ι ι R, BlockSupported blk i j M ∧ mat g = 1 + M := Iff.rfl

theorem blockElement_mem (blk : ι → Fin 3) (i j : Fin 3) (hij : i ≠ j)
    (M : Matrix ι ι R) (hM : BlockSupported blk i j M) :
    blockElement blk i j hij M hM ∈ blockRootSubgroup blk i j hij :=
  ⟨M, hM, rfl⟩

/-- The union of the six rectangular block roots. -/
def blockRootSet (blk : ι → Fin 3) : Set (elementaryGroup ι R) :=
  {g | ∃ (i j : Fin 3) (hij : i ≠ j), g ∈ blockRootSubgroup blk i j hij}

theorem elementaryRoot_mem_blockRootSet (blk : ι → Fin 3) {u v : ι}
    (huv : u ≠ v) (hb : blk u ≠ blk v) (a : R) :
    elementaryRoot u v huv a ∈ blockRootSet (R := R) blk :=
  ⟨blk u, blk v, hb, Matrix.single u v a, blockSupported_single rfl rfl a, rfl⟩

/-- The commutator of two composable rectangular blocks. -/
theorem mat_commutator (blk : ι → Fin 3) {i j k : Fin 3} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) {x y : elementaryGroup ι R}
    {M N : Matrix ι ι R} (hM : BlockSupported blk i j M)
    (hN : BlockSupported blk j k N) (hx : mat x = 1 + M) (hy : mat y = 1 + N) :
    mat ⁅x, y⁆ = 1 + M * N := by
  have hMM : M * M = 0 := BlockSupported.mul_self hij hM
  have hNN : N * N = 0 := BlockSupported.mul_self hjk hN
  have hNM : N * M = 0 := mul_eq_zero_of_blockSupported hN hM hik.symm
  have hPM : M * N * M = 0 :=
    mul_eq_zero_of_blockSupported (hM.mul hN) hM hik.symm
  have hPN : M * N * N = 0 :=
    mul_eq_zero_of_blockSupported (hM.mul hN) hN hjk.symm
  rw [commutatorElement_def, mat_mul, mat_mul, mat_mul,
    mat_inv x hMM hx, mat_inv y hNN hy, hx, hy]
  noncomm_ring [hMM, hNN, hNM, hPM, hPN]

theorem blockRoot_commute (blk : ι → Fin 3) :
    ∀ (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ x ∈ blockRootSubgroup (R := R) blk i j hij,
        ∀ y ∈ blockRootSubgroup (R := R) blk k l hkl, Commute x y := by
  rintro i j k l hij hkl hjk hli x ⟨M, hM, hx⟩ y ⟨N, hN, hy⟩
  have h1 : M * N = 0 := mul_eq_zero_of_blockSupported hM hN hjk
  have h2 : N * M = 0 := mul_eq_zero_of_blockSupported hN hM hli
  show x * y = y * x
  refine mat_injective ?_
  rw [mat_mul, mat_mul, hx, hy]
  noncomm_ring [h1, h2]

theorem blockRoot_commutator_mem (blk : ι → Fin 3) :
    ∀ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      ∀ x ∈ blockRootSubgroup (R := R) blk i j hij,
        ∀ y ∈ blockRootSubgroup (R := R) blk j k hjk,
          ⁅x, y⁆ ∈ blockRootSubgroup (R := R) blk i k hik := by
  rintro i j k hij hjk hik x ⟨M, hM, hx⟩ y ⟨N, hN, hy⟩
  exact ⟨M * N, hM.mul hN, mat_commutator blk hij hjk hik hM hN hx hy⟩

theorem blockRoot_commutator_surjective (blk : ι → Fin 3)
    (hfactor : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      ∀ Z : Matrix ι ι R, BlockSupported blk i k Z →
        ∃ X Y : Matrix ι ι R, BlockSupported blk i j X ∧
          BlockSupported blk j k Y ∧ X * Y = Z) :
    ∀ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      ∀ z ∈ blockRootSubgroup (R := R) blk i k hik,
        ∃ x ∈ blockRootSubgroup (R := R) blk i j hij,
          ∃ y ∈ blockRootSubgroup (R := R) blk j k hjk, ⁅x, y⁆ = z := by
  rintro i j k hij hjk hik z ⟨Z, hZ, hz⟩
  obtain ⟨X, Y, hX, hY, hXY⟩ := hfactor i j k hij hjk hik Z hZ
  refine ⟨blockElement blk i j hij X hX, blockElement_mem blk i j hij X hX,
    blockElement blk j k hjk Y hY, blockElement_mem blk j k hjk Y hY, ?_⟩
  refine mat_injective ?_
  rw [mat_commutator blk hij hjk hik hX hY (mat_blockElement blk i j hij X hX)
    (mat_blockElement blk j k hjk Y hY), hXY, hz]

theorem blockRootSet_generate (blk : ι → Fin 3)
    (hsurj : Function.Surjective blk) :
    Subgroup.closure (blockRootSet (R := R) blk) = ⊤ := by
  apply top_unique
  rw [← elementaryRootSet_generate (I := ι) (R := R), Subgroup.closure_le]
  rintro g ⟨u, v, huv, a, rfl⟩
  by_cases hb : blk u = blk v
  · obtain ⟨w, hw⟩ := exists_ne (blk u)
    obtain ⟨t, ht⟩ := hsurj w
    have hbut : blk u ≠ blk t := by
      rw [ht]
      exact fun h => hw h.symm
    have hbtv : blk t ≠ blk v := by
      rw [← hb]
      exact fun h => hbut h.symm
    have hut : u ≠ t := fun h => hbut (by rw [h])
    have htv : t ≠ v := fun h => hbtv (by rw [h])
    have hxc : elementaryRoot u t hut a ∈
        Subgroup.closure (blockRootSet (R := R) blk) :=
      Subgroup.subset_closure (elementaryRoot_mem_blockRootSet blk hut hbut a)
    have hyc : elementaryRoot t v htv (1 : R) ∈
        Subgroup.closure (blockRootSet (R := R) blk) :=
      Subgroup.subset_closure (elementaryRoot_mem_blockRootSet blk htv hbtv 1)
    have hcomm : ⁅elementaryRoot u t hut a, elementaryRoot t v htv (1 : R)⁆ ∈
        Subgroup.closure (blockRootSet (R := R) blk) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxc hyc) (inv_mem hxc)) (inv_mem hyc)
    rw [elementaryRoot_commutator u t v hut htv huv a 1, mul_one] at hcomm
    exact hcomm
  · exact Subgroup.subset_closure
      (elementaryRoot_mem_blockRootSet blk huv hb a)

/-- **The rectangular three-block `A₂` system inside `EL_ι(R)`.**  Unlike
`SteinbergBlockRoot.blockA2System`, no `CompleteMatrixFamily` is involved:
the root subgroups are genuine rectangular transvection groups.

Both hypotheses are algebraic conditions on the partition alone.  `hsurj`
says all three blocks are nonempty.  `hfactor` says every rectangular block
factors through the third block; it holds whenever at most one block has
more than one element (see `finBlock_exists_factor`), and it is exactly the
condition that fails for an equal-thirds partition of `Fin n` when
`3 ∤ n`. -/
def blockA2System (blk : ι → Fin 3) (hsurj : Function.Surjective blk)
    (hfactor : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      ∀ Z : Matrix ι ι R, BlockSupported blk i k Z →
        ∃ X Y : Matrix ι ι R, BlockSupported blk i j X ∧
          BlockSupported blk j k Y ∧ X * Y = Z) :
    A2System (elementaryGroup ι R) where
  root := blockRootSubgroup blk
  generate := blockRootSet_generate blk hsurj
  commute := blockRoot_commute blk
  commutator_mem := blockRoot_commutator_mem blk
  commutator_surjective := blockRoot_commutator_surjective blk hfactor

/-- In characteristic `p` every rectangular block root element has exponent
dividing `p`.  This is the bounded-exponent input of the magic-graph
theorem. -/
theorem blockRootSubgroup_pow_char (blk : ι → Fin 3) (p : ℕ) [CharP R p]
    (i j : Fin 3) (hij : i ≠ j) (g : elementaryGroup ι R)
    (hg : g ∈ blockRootSubgroup blk i j hij) : g ^ p = 1 := by
  obtain ⟨M, hM, hgm⟩ := hg
  refine mat_injective ?_
  rw [mat_one, mat_pow, hgm, one_add_pow M (BlockSupported.mul_self hij hM) p,
    char_nsmul_eq_zero p M, add_zero]

/-- The rectangular block root union of `EL_ι(R)` is a Kazhdan subset, for
every three-block partition satisfying the two algebraic conditions and
every ring of positive characteristic. -/
theorem blockA2System_exists_rootSet_isKazhdan (blk : ι → Fin 3)
    (hsurj : Function.Surjective blk)
    (hfactor : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      ∀ Z : Matrix ι ι R, BlockSupported blk i k Z →
        ∃ X Y : Matrix ι ι R, BlockSupported blk i j X ∧
          BlockSupported blk j k Y ∧ X * Y = Z)
    (p : ℕ) (hp : 0 < p) [CharP R p] :
    ∃ kappa : ℝ, IsKazhdanSubset (elementaryGroup ι R)
      (blockA2System blk hsurj hfactor).rootSet kappa := by
  refine A2MagicHilbert.exists_rootSet_isKazhdan _ p hp ?_
  intro i j hij g hg
  exact blockRootSubgroup_pow_char blk p i j hij g hg

end Roots

/-! ### Factoring a rectangular block through a singleton block -/

section Factor

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

theorem single_diag_mul_eq_self (blk : ι → Fin 3) {i k : Fin 3} (u : ι)
    (husing : ∀ a : ι, blk a = i → a = u) (Z : Matrix ι ι R)
    (hZ : BlockSupported blk i k Z) :
    Matrix.single u u (1 : R) * Z = Z := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hau : u = a
  · subst hau
    rw [Fintype.sum_eq_single u]
    · rw [Matrix.single_apply_same, one_mul]
    · intro d hdu
      rw [Matrix.single_apply_of_ne u u (1 : R) u d (fun h => hdu h.2.symm),
        zero_mul]
  · have hai : blk a ≠ i := fun hb => hau (husing a hb).symm
    rw [hZ.row hai]
    refine Finset.sum_eq_zero ?_
    intro d _
    rw [Matrix.single_apply_of_ne u u (1 : R) a d (fun h => hau h.1), zero_mul]

theorem single_mul_diag_eq_self (blk : ι → Fin 3) {i k : Fin 3} (v : ι)
    (hvsing : ∀ b : ι, blk b = k → b = v) (Z : Matrix ι ι R)
    (hZ : BlockSupported blk i k Z) :
    Z * Matrix.single v v (1 : R) = Z := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hbv : v = b
  · subst hbv
    rw [Fintype.sum_eq_single v]
    · rw [Matrix.single_apply_same, mul_one]
    · intro d hdv
      rw [Matrix.single_apply_of_ne v v (1 : R) d v (fun h => hdv h.1.symm),
        mul_zero]
  · have hbk : blk b ≠ k := fun hc => hbv (hvsing b hc).symm
    rw [hZ.col hbk]
    refine Finset.sum_eq_zero ?_
    intro d _
    rw [Matrix.single_apply_of_ne v v (1 : R) d b (fun h => hbv h.2), mul_zero]

/-- If the source block is a singleton, every rectangular block factors
through any nonempty middle block. -/
theorem exists_factor_of_left_singleton (blk : ι → Fin 3) {i j k : Fin 3}
    (u t : ι) (hu : blk u = i) (husing : ∀ a : ι, blk a = i → a = u)
    (ht : blk t = j) (Z : Matrix ι ι R) (hZ : BlockSupported blk i k Z) :
    ∃ X Y : Matrix ι ι R, BlockSupported blk i j X ∧
      BlockSupported blk j k Y ∧ X * Y = Z := by
  refine ⟨Matrix.single u t 1, Matrix.single t u 1 * Z,
    blockSupported_single hu ht 1,
    BlockSupported.mul (blockSupported_single ht hu 1) hZ, ?_⟩
  rw [← mul_assoc, Matrix.single_mul_single_same, one_mul]
  exact single_diag_mul_eq_self blk u husing Z hZ

/-- If the target block is a singleton, every rectangular block factors
through any nonempty middle block. -/
theorem exists_factor_of_right_singleton (blk : ι → Fin 3) {i j k : Fin 3}
    (t v : ι) (ht : blk t = j) (hv : blk v = k)
    (hvsing : ∀ b : ι, blk b = k → b = v) (Z : Matrix ι ι R)
    (hZ : BlockSupported blk i k Z) :
    ∃ X Y : Matrix ι ι R, BlockSupported blk i j X ∧
      BlockSupported blk j k Y ∧ X * Y = Z := by
  refine ⟨Z * Matrix.single v t 1, Matrix.single t v 1,
    BlockSupported.mul hZ (blockSupported_single hv ht 1),
    blockSupported_single ht hv 1, ?_⟩
  rw [mul_assoc, Matrix.single_mul_single_same, one_mul]
  exact single_mul_diag_eq_self blk v hvsing Z hZ

end Factor

/-! ### The partition `{0}`, `{1}`, tail of `Fin n` -/

section FinBlock

/-- The three-block partition of `Fin n` into `{0}`, `{1}` and the tail. -/
def finBlock (n : ℕ) (a : Fin n) : Fin 3 := ⟨min a.val 2, by omega⟩

theorem finBlock_eq_iff (n : ℕ) (a : Fin n) (i : Fin 3) :
    finBlock n a = i ↔ min a.val 2 = i.val :=
  Fin.ext_iff

theorem finBlock_surjective (n : ℕ) (hn : 3 ≤ n) :
    Function.Surjective (finBlock n) := by
  intro i
  have h3 : i.val < 3 := i.isLt
  refine ⟨⟨i.val, by omega⟩, ?_⟩
  rw [finBlock_eq_iff]
  show min i.val 2 = i.val
  omega

/-- The two low blocks are singletons. -/
theorem finBlock_eq_of_lt_two (n : ℕ) {a b : Fin n} {i : Fin 3} (hi : i.val < 2)
    (ha : finBlock n a = i) (hb : finBlock n b = i) : a = b := by
  rw [finBlock_eq_iff] at ha hb
  exact Fin.ext (by omega)

/-- With two singleton blocks the factorization condition holds at every
vertex, for every `n ≥ 3`. -/
theorem finBlock_exists_factor (R : Type*) [Ring R] (n : ℕ) (hn : 3 ≤ n) :
    ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      ∀ Z : Matrix (Fin n) (Fin n) R, BlockSupported (finBlock n) i k Z →
        ∃ X Y : Matrix (Fin n) (Fin n) R,
          BlockSupported (finBlock n) i j X ∧
            BlockSupported (finBlock n) j k Y ∧ X * Y = Z := by
  intro i j k _ _ hik Z hZ
  obtain ⟨t, ht⟩ := finBlock_surjective n hn j
  by_cases hi2 : i.val < 2
  · obtain ⟨u, hu⟩ := finBlock_surjective n hn i
    exact exists_factor_of_left_singleton (finBlock n) u t hu
      (fun a ha => finBlock_eq_of_lt_two n hi2 ha hu) ht Z hZ
  · have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have h1 : i.val < 3 := i.isLt
    have h2 : k.val < 3 := k.isLt
    have hk2 : k.val < 2 := by omega
    obtain ⟨v, hv⟩ := finBlock_surjective n hn k
    exact exists_factor_of_right_singleton (finBlock n) t v ht hv
      (fun b hb => finBlock_eq_of_lt_two n hk2 hb hv) Z hZ

/-- **The rectangular block `A₂` system of `EL_n(R)` for every `n ≥ 3` and
every ring `R`.**  No characteristic, finiteness or self-similarity
hypothesis is used. -/
def blockElementaryA2System (R : Type*) [Ring R] (n : ℕ) (hn : 3 ≤ n) :
    A2System (elementaryGroup (Fin n) R) :=
  blockA2System (finBlock n) (finBlock_surjective n hn)
    (finBlock_exists_factor R n hn)

/-- **The union of the six rectangular block roots of `EL_n(R)` is a Kazhdan
subset, for every `n ≥ 3` and every ring of positive characteristic.**

This is the rank-general form of
`A2MagicHilbert.elementary_exists_rootSet_isKazhdan`, and the rank-general,
`CompleteMatrixFamily`-free form of
`SteinbergBlockRoot.blockA2_exists_rootSet_isKazhdan`. -/
theorem blockElementary_exists_rootSet_isKazhdan (R : Type*) [Ring R] (p : ℕ)
    (hp : 0 < p) [CharP R p] (n : ℕ) (hn : 3 ≤ n) :
    ∃ kappa : ℝ, IsKazhdanSubset (elementaryGroup (Fin n) R)
      (blockElementaryA2System R n hn).rootSet kappa :=
  blockA2System_exists_rootSet_isKazhdan (finBlock n) (finBlock_surjective n hn)
    (finBlock_exists_factor R n hn) p hp

end FinBlock

/-! ### Displacement by a rectangular block -/

section Displacement

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

private theorem norm_displacement_blockRestrict_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {blk : ι → Fin 3}
    {i j : Fin 3} (hij : i ≠ j)
    (rho : elementaryGroup ι R →* (E ≃ₗᵢ[ℝ] E)) (z : E) (D : ℝ) (hD : 0 ≤ D)
    (hroot : ∀ (u v : ι) (huv : u ≠ v) (c : R),
      ‖rho (elementaryRoot u v huv c) z - z‖ ≤ D)
    {M : Matrix ι ι R} (hM : BlockSupported blk i j M) :
    ∀ (s : Finset (ι × ι)) (g : elementaryGroup ι R),
      mat g = 1 + blockRestrict M s → ‖rho g z - z‖ ≤ (s.card : ℝ) * D := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro g hg
      have hg1 : g = 1 := mat_injective (by simp [hg])
      rw [hg1]
      simp
  | insert p s hs ih =>
      obtain ⟨u, v⟩ := p
      intro g hg
      rw [Finset.card_insert_of_notMem hs, Nat.cast_add, Nat.cast_one, add_mul,
        one_mul]
      by_cases hc : M u v = 0
      · have hle : ‖rho g z - z‖ ≤ (s.card : ℝ) * D := by
          refine ih g ?_
          rw [hg, blockRestrict_insert M u v s hs, hc, Matrix.single_zero,
            zero_add]
        linarith
      · have hbu : blk u = i := (hM u v hc).1
        have hbv : blk v = j := (hM u v hc).2
        have huv : u ≠ v := by
          intro h
          refine hij ?_
          rw [← hbu, ← hbv, h]
        have hNsupp : BlockSupported blk i j (blockRestrict M s) :=
          blockRestrict_blockSupported hM s
        obtain ⟨w, hw⟩ : ∃ w : elementaryGroup ι R,
            mat w = 1 + blockRestrict M s :=
          ⟨blockElement blk i j hij (blockRestrict M s) hNsupp,
            mat_blockElement blk i j hij (blockRestrict M s) hNsupp⟩
        have hz0 : Matrix.single u v (M u v) * blockRestrict M s = 0 :=
          mul_eq_zero_of_blockSupported (blockSupported_single hbu hbv _)
            hNsupp hij.symm
        have hgw : g = elementaryRoot u v huv (M u v) * w := by
          refine mat_injective ?_
          rw [hg, mat_mul, blockRestrict_insert M u v s hs,
            mat_elementaryRoot, hw]
          noncomm_ring [hz0]
        have h1 := hroot u v huv (M u v)
        have h2 := ih w hw
        rw [hgw]
        refine (A2System.norm_mul_displacement_le rho z _ _).trans ?_
        linarith

/-- Displacement by a rectangular block is bounded by the number of matrix
positions times the displacement by a single elementary transvection. -/
theorem norm_blockRoot_displacement_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {blk : ι → Fin 3} {i j : Fin 3} (hij : i ≠ j)
    (rho : elementaryGroup ι R →* (E ≃ₗᵢ[ℝ] E)) (z : E) (D : ℝ) (hD : 0 ≤ D)
    (hroot : ∀ (u v : ι) (huv : u ≠ v) (c : R),
      ‖rho (elementaryRoot u v huv c) z - z‖ ≤ D)
    (g : elementaryGroup ι R) (hg : g ∈ blockRootSubgroup blk i j hij) :
    ‖rho g z - z‖ ≤ ((Fintype.card ι * Fintype.card ι : ℕ) : ℝ) * D := by
  obtain ⟨M, hM, hgm⟩ := hg
  have hle := norm_displacement_blockRestrict_le hij rho z D hD hroot hM
    Finset.univ g (by rw [hgm, blockRestrict_univ])
  rwa [Finset.card_univ, Fintype.card_prod] at hle

end Displacement

/-! ### Property `(T)` in every rank at least three, in characteristic two -/

noncomputable section

open SteinbergHigherRankFiniteControl

universe w

variable (X : Type) [Fintype X]

/-- The higher-rank Steinberg control set, pushed to the elementary group
along the canonical surjection `St_n(R) ↠ EL_n(R)`. -/
def elementaryControlSet (n : ℕ) :
    Finset (elementaryGroup (Fin n) (SteinbergRootPlaneFourier.FreeRing X)) := by
  classical
  exact (finiteControlSetAt X n).image (SteinbergGroup.projection (I := Fin n))

/-- The descended control set bounds displacement by every *ordinary*
elementary root, in every rank at least three. -/
theorem elementaryControlSet_controls_rootSet (n : ℕ) (hn : 3 ≤ n) :
    ControlsSubsetDisplacement
      (elementaryGroup (Fin n) (SteinbergRootPlaneFourier.FreeRing X))
      (elementaryControlSet X n)
      (elementaryRootSet (Fin n) (SteinbergRootPlaneFourier.FreeRing X))
      (12 * Fintype.card X + 13 : ℝ) := by
  classical
  intro E _ _ _ rho z hz δ hδ hnear g hg
  obtain ⟨u, v, huv, a, rfl⟩ := hg
  have hnear' : ∀ s ∈ finiteControlSetAt X n,
      ‖(rho.comp (SteinbergGroup.projection (I := Fin n))) s z - z‖ < δ := by
    intro s hsmem
    exact hnear _ (Finset.mem_image.mpr ⟨s, hsmem, rfl⟩)
  have hroot : SteinbergGroup.x u v huv a ∈
      SteinbergGroup.rootSet (I := Fin n) (R := SteinbergRootPlaneFourier.FreeRing X) :=
    ⟨u, v, huv, ⟨a, rfl⟩⟩
  have hmove := finiteControlSetAt_controls_rootSet X n hn E
    (rho.comp (SteinbergGroup.projection (I := Fin n))) z hz δ hδ hnear' _ hroot
  simpa using hmove

/-- The same finite set controls the six rectangular block roots, with only
the finite loss `n²`. -/
theorem elementaryControlSet_controls_blockRootSet (n : ℕ) (hn : 3 ≤ n) :
    ControlsSubsetDisplacement
      (elementaryGroup (Fin n) (SteinbergRootPlaneFourier.FreeRing X))
      (elementaryControlSet X n)
      (blockElementaryA2System (SteinbergRootPlaneFourier.FreeRing X) n hn).rootSet
      ((n * n : ℕ) * (12 * Fintype.card X + 13 : ℝ) + 1) := by
  intro E _ _ _ rho z hz δ hδ hnear g hg
  obtain ⟨i, j, hij, hgm⟩ := hg
  have hord := elementaryControlSet_controls_rootSet X n hn E rho z hz δ hδ hnear
  have hCpos : (0 : ℝ) < 12 * Fintype.card X + 13 := by positivity
  have hD : (0 : ℝ) ≤ (12 * Fintype.card X + 13 : ℝ) * δ :=
    le_of_lt (mul_pos hCpos hδ)
  have hroot : ∀ (u v : Fin n) (huv : u ≠ v) (c : SteinbergRootPlaneFourier.FreeRing X),
      ‖rho (elementaryRoot u v huv c) z - z‖ ≤
        (12 * Fintype.card X + 13 : ℝ) * δ := by
    intro u v huv c
    exact le_of_lt (hord _ ⟨u, v, huv, c, rfl⟩)
  have hbound := norm_blockRoot_displacement_le (blk := finBlock n) hij rho z _
    hD hroot g hgm
  rw [Fintype.card_fin] at hbound
  nlinarith [hbound, hδ, hCpos]

/-- The descended control set is a genuine finite Kazhdan pair for `EL_n` of
the free characteristic-two algebra, in every rank `n ≥ 3`. -/
theorem elementaryControlSet_isKazhdanPair (n : ℕ) (hn : 3 ≤ n) :
    ∃ epsilon : ℝ,
      IsKazhdanPair.{0, w} (elementaryGroup (Fin n) (SteinbergRootPlaneFourier.FreeRing X))
        (elementaryControlSet X n) epsilon := by
  obtain ⟨kappa, hkappa⟩ :=
    blockElementary_exists_rootSet_isKazhdan
      (SteinbergRootPlaneFourier.FreeRing X) 2 (by omega) n hn
  have hC : (0 : ℝ) < (n * n : ℕ) * (12 * Fintype.card X + 13 : ℝ) + 1 := by
    positivity
  exact ⟨kappa / (2 * ((n * n : ℕ) * (12 * Fintype.card X + 13 : ℝ) + 1)),
    IsKazhdanSubset.to_pair_of_controls hkappa hC
      (elementaryControlSet_controls_blockRootSet X n hn)⟩

/-- Elementary rank `n ≥ 3` over the free characteristic-two algebra on a
finite generating set has Kazhdan's property `(T)`. -/
theorem freeBlockElementary_hasKazhdanPropertyT (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, w}
      (elementaryGroup (Fin n) (SteinbergRootPlaneFourier.FreeRing X)) := by
  obtain ⟨epsilon, hpair⟩ := elementaryControlSet_isKazhdanPair X n hn
  exact ⟨elementaryControlSet X n, epsilon, hpair⟩

end

/-- The general-rank, characteristic-two form of the Ershov--Jaikin-Zapirain
theorem proved in this file: property `(T)` for `EL_n(R)` in *every* rank
`n ≥ 3` over *every* finite-type `ZMod 2`-algebra.

This is the statement the rectangular block system buys, given the finite
control sets the tree already has.  The printed Ershov--Jaikin-Zapirain
statement is stronger in the base ring: it allows every finitely generated
unital associative ring, in particular characteristic zero.  Nothing in this
file addresses that axis. -/
def CharTwoGeneralRankElementaryPropertyT : Prop :=
  ∀ (R : Type) [Ring R] [Algebra (ZMod 2) R] [Algebra.FiniteType (ZMod 2) R]
    (n : ℕ), 3 ≤ n → HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) R)

/-- **Property `(T)` for `EL_n(R)` in every rank `n ≥ 3` over every
finite-type `ZMod 2`-algebra.**  Rank three is
`finiteTypeElementaryThree_hasKazhdanPropertyT`; the higher ranks are new,
and unlike `SteinbergHigherRankPropertyT` they need no
`CompleteMatrixFamily`. -/
theorem finiteTypeCharTwoElementary_hasKazhdanPropertyT
    {R : Type} [Ring R] [Algebra (ZMod 2) R] [Algebra.FiniteType (ZMod 2) R]
    (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) R) := by
  obtain ⟨X, hX, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_freeAlgebra'
      (R := ZMod 2) (A := R)).mp inferInstance
  letI : Fintype X := hX
  exact HasKazhdanPropertyT.of_surjective
    (elementaryGroupMap (ι := Fin n) f.toRingHom)
    (elementaryGroupMap_surjective_of_surjective f.toRingHom hf)
    (freeBlockElementary_hasKazhdanPropertyT X n hn)

theorem charTwoGeneralRankElementaryPropertyT :
    CharTwoGeneralRankElementaryPropertyT := by
  intro R _ _ _ n hn
  exact finiteTypeCharTwoElementary_hasKazhdanPropertyT n hn

end BlockElementary
end GroupApproximation
