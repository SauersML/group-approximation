import GroupApproximation.Algebra.PeirceTwistedMatrixRing
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
# Elementary matrices of a Peirce decomposition, and two-sided factorisation

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`, item (a), the
clause after the matrix identification:

> … and every unit `u` of `R` factors as `u = gvh` with `g` and `h` products of
> elementary matrices `e_{ij}(x)` of this matrix ring and
> `v = e_1 + (1-e_1)v(1-e_1)`.

This module supplies the two notions that clause needs, and nothing else: the
elementary matrices themselves, and the factorisation relation.

## The elementary matrices, in `R`

Under the identification of `Algebra/PeirceTwistedMatrixRing.lean`, the
elementary matrix `e_{ij}(x)` of the matrix ring is the unit `1 + x` of `R`
with `x` in the block `e_i R e_j`, `i ≠ j`.  That is `IsPeirceElementary`, and
`peirceElementarySubgroup` is the group they generate — the printed "products
of elementary matrices `e_{ij}(x)` of this matrix ring".

## Coarse transvections are already products of elementary matrices

The reduction argument produces units `1 + x` with `x` in `e_k R (1 - e_k)`,
which is a *sum* of blocks rather than a single one.  Such a unit is
nevertheless a product of elementary matrices, with no group theory at all:
writing `x = ∑_{i ≠ k} x e_i`, the pieces annihilate each other, so

    `1 + x = ∏_{i ≠ k} (1 + x e_i)`

and each factor is a single `e_{ki}(x e_i)`.  That is `peirceOneAdd_of_left`,
and `peirceOneAdd_of_right` is the transposed statement.  This is what lets the
whole reduction be carried out inside the elementary subgroup, which is **not**
known to be normal, instead of inside `cornerUnitSubgroup`, which is normal but
is a different group.

## Why a two-sided relation

`Manuscript/OneSidedMFRadical/MFQuotientUnitsReductionProof.lean` records its
reduction as `Peirce.Congr N u v`, that is `u * v⁻¹ ∈ N`, and its transitivity
on the right needs `N` normal.  The printed clause asks instead for a two-sided
factorisation `u = g v h`, and that relation — `FactorsThrough` below — is
reflexive, transitive, and closed under multiplying on either side by an
element of `N` **without any normality assumption**.  So it is the right
bookkeeping for the elementary subgroup.

## Universes

`Peirce.squareZeroUnit` and `Peirce.OneAddIn` are the same constructions, but
their section fixes `R : Type`.  Everything here is stated at `Type*`, so the
unit `1 + x` is built directly.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-! ### The unit `1 + x` for a square-zero `x` -/

/-- The unit `1 + x`, for `x` with `x * x = 0`, with its inverse `1 - x`. -/
def oneAddSquareZero {x : R} (hx : x * x = 0) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by noncomm_ring [hx]
  inv_val := by noncomm_ring [hx]

@[simp] theorem coe_oneAddSquareZero {x : R} (hx : x * x = 0) :
    (oneAddSquareZero hx : R) = 1 + x := rfl

section Elementary

variable {ι : Type*}

/-! ### The printed elementary matrices `e_{ij}(x)` -/

/-- **The printed elementary matrix `e_{ij}(x)` of the Peirce matrix ring**,
read inside `R`: a unit `1 + x` whose `x` lies in the block `e_i R e_j` for two
distinct indices. -/
def IsPeirceElementary (e : ι → R) (w : Rˣ) : Prop :=
  ∃ (i j : ι) (x : R), i ≠ j ∧ e i * x = x ∧ x * e j = x ∧ (w : R) = 1 + x

/-- **The printed "products of elementary matrices `e_{ij}(x)` of this matrix
ring"**: the subgroup of `Rˣ` they generate.  Each generator is its own
inverse's negation, `(1 + x)⁻¹ = 1 - x`, so this subgroup is exactly the set of
finite products of elementary matrices. -/
def peirceElementarySubgroup (e : ι → R) : Subgroup Rˣ :=
  Subgroup.closure {w : Rˣ | IsPeirceElementary e w}

/-- `x` is realised by a product of elementary matrices, as `1 + x`. -/
def PeirceOneAdd (e : ι → R) (x : R) : Prop :=
  ∃ w ∈ peirceElementarySubgroup e, (w : R) = 1 + x

theorem peirceOneAdd_zero (e : ι → R) : PeirceOneAdd e 0 :=
  ⟨1, (peirceElementarySubgroup e).one_mem, by simp⟩

/-- A single block gives a single elementary matrix. -/
theorem peirceOneAdd_of_block (e : ι → R) {i j : ι} (hij : i ≠ j)
    (horth : e j * e i = 0) {x : R} (hi : e i * x = x) (hj : x * e j = x) :
    PeirceOneAdd e x := by
  have hxx : x * x = 0 := by
    calc x * x = (x * e j) * (e i * x) := by rw [hj, hi]
      _ = x * (e j * e i) * x := by noncomm_ring
      _ = 0 := by rw [horth]; simp
  exact ⟨oneAddSquareZero hxx,
    Subgroup.subset_closure ⟨i, j, x, hij, hi, hj, rfl⟩, rfl⟩

/-- Pairwise annihilating pieces multiply their `1 + ·` units into `1 + ∑`. -/
theorem peirceOneAdd_sum (e : ι → R) {κ : Type*} (z : κ → R) (s : Finset κ) :
    (∀ a ∈ s, ∀ b ∈ s, z a * z b = 0) → (∀ a ∈ s, PeirceOneAdd e (z a)) →
      PeirceOneAdd e (∑ a ∈ s, z a) := by
  classical
  induction s using Finset.induction with
  | empty => intro _ _; simpa using peirceOneAdd_zero e
  | insert a s ha ih =>
      intro hzero hmem
      obtain ⟨w, hw, hwv⟩ := hmem a (Finset.mem_insert_self a s)
      obtain ⟨w', hw', hwv'⟩ := ih
        (fun b hb c hc => hzero b (Finset.mem_insert_of_mem hb) c
          (Finset.mem_insert_of_mem hc))
        (fun b hb => hmem b (Finset.mem_insert_of_mem hb))
      refine ⟨w * w', (peirceElementarySubgroup e).mul_mem hw hw', ?_⟩
      have hcross : z a * ∑ b ∈ s, z b = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun b hb =>
          hzero a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
      rw [Units.val_mul, hwv, hwv', Finset.sum_insert ha]
      calc (1 + z a) * (1 + ∑ b ∈ s, z b)
          = 1 + z a + ∑ b ∈ s, z b + z a * ∑ b ∈ s, z b := by noncomm_ring
        _ = 1 + (z a + ∑ b ∈ s, z b) := by rw [hcross]; abel

/-! ### Coarse transvections -/

theorem block_mul_eq_zero (e : ι → R)
    (horth : ∀ i j : ι, i ≠ j → e i * e j = 0) {k i : ι} (hik : i ≠ k) {x : R}
    (hk : e k * x = x) : e i * x = 0 := by
  calc e i * x = e i * (e k * x) := by rw [hk]
    _ = (e i * e k) * x := by noncomm_ring
    _ = 0 := by rw [horth i k hik, zero_mul]

theorem mul_block_eq_zero (e : ι → R)
    (horth : ∀ i j : ι, i ≠ j → e i * e j = 0) {k i : ι} (hik : i ≠ k) {x : R}
    (hk : x * e k = x) : x * e i = 0 := by
  calc x * e i = (x * e k) * e i := by rw [hk]
    _ = x * (e k * e i) := by noncomm_ring
    _ = 0 := by rw [horth k i (Ne.symm hik), mul_zero]

theorem sum_erase_eq [Fintype ι] [DecidableEq ι] (e : ι → R)
    (hsum : ∑ i, e i = 1) (k : ι) :
    ∑ i ∈ Finset.univ.erase k, e i = 1 - e k := by
  have h := Finset.add_sum_erase Finset.univ e (Finset.mem_univ k)
  rw [hsum] at h
  exact eq_sub_of_add_eq' h

/-- **A transvection supported on one block row is a product of elementary
matrices.**  `x ∈ e_k R (1 - e_k)` splits along the blocks, and the pieces
annihilate one another. -/
theorem peirceOneAdd_of_left [Fintype ι] [DecidableEq ι] (e : ι → R)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : ι, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1)
    (k : ι) {x : R} (hk : e k * x = x) (hxk : x * e k = 0) :
    PeirceOneAdd e x := by
  classical
  have hsplit : ∑ i ∈ Finset.univ.erase k, x * e i = x := by
    rw [← Finset.mul_sum, sum_erase_eq e hsum k, mul_sub, hxk, sub_zero, mul_one]
  rw [← hsplit]
  refine peirceOneAdd_sum e _ _ (fun a ha b _ => ?_) (fun a ha => ?_)
  · have hak : a ≠ k := Finset.ne_of_mem_erase ha
    calc x * e a * (x * e b) = x * (e a * x) * e b := by noncomm_ring
      _ = 0 := by rw [block_mul_eq_zero e horth hak hk, mul_zero, zero_mul]
  · have hak : a ≠ k := Finset.ne_of_mem_erase ha
    refine peirceOneAdd_of_block e (Ne.symm hak) (horth a k hak) ?_ ?_
    · rw [← mul_assoc, hk]
    · rw [mul_assoc, hidem a]

/-- **A transvection supported on one block column is a product of elementary
matrices.**  The transpose of `peirceOneAdd_of_left`. -/
theorem peirceOneAdd_of_right [Fintype ι] [DecidableEq ι] (e : ι → R)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : ι, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1)
    (k : ι) {x : R} (hk : x * e k = x) (hxk : e k * x = 0) :
    PeirceOneAdd e x := by
  classical
  have hsplit : ∑ i ∈ Finset.univ.erase k, e i * x = x := by
    rw [← Finset.sum_mul, sum_erase_eq e hsum k, sub_mul, hxk, sub_zero, one_mul]
  rw [← hsplit]
  refine peirceOneAdd_sum e _ _ (fun a _ b hb => ?_) (fun a ha => ?_)
  · have hbk : b ≠ k := Finset.ne_of_mem_erase hb
    calc e a * x * (e b * x) = e a * (x * e b) * x := by noncomm_ring
      _ = 0 := by rw [mul_block_eq_zero e horth hbk hk, mul_zero, zero_mul]
  · have hak : a ≠ k := Finset.ne_of_mem_erase ha
    refine peirceOneAdd_of_block e hak (horth k a (Ne.symm hak)) ?_ ?_
    · rw [← mul_assoc, hidem a]
    · rw [mul_assoc, hk]

end Elementary

/-! ### The two-sided factorisation relation -/

/-- **The printed `u = gvh`**, for a fixed group `N` of allowed factors.

Unlike the one-sided coset relation, this needs no normality: the printed
clause asks for factors on both sides, and that is exactly what makes the
relation transitive for an arbitrary subgroup. -/
def FactorsThrough (N : Subgroup Rˣ) (u v : Rˣ) : Prop :=
  ∃ g h : Rˣ, g ∈ N ∧ h ∈ N ∧ u = g * v * h

namespace FactorsThrough

variable {N : Subgroup Rˣ} {u v w : Rˣ}

theorem refl (N : Subgroup Rˣ) (u : Rˣ) : FactorsThrough N u u :=
  ⟨1, 1, N.one_mem, N.one_mem, by group⟩

theorem trans (h : FactorsThrough N u v) (h' : FactorsThrough N v w) :
    FactorsThrough N u w := by
  obtain ⟨g, k, hg, hk, huv⟩ := h
  obtain ⟨g', k', hg', hk', hvw⟩ := h'
  refine ⟨g * g', k' * k, N.mul_mem hg hg', N.mul_mem hk' hk, ?_⟩
  rw [huv, hvw]
  group

/-- Multiplying on the left by an allowed factor. -/
theorem left (N : Subgroup Rˣ) (u w : Rˣ) (hw : w ∈ N) :
    FactorsThrough N u (w * u) :=
  ⟨w⁻¹, 1, N.inv_mem hw, N.one_mem, by group⟩

/-- Multiplying on the right by an allowed factor. -/
theorem right (N : Subgroup Rˣ) (u w : Rˣ) (hw : w ∈ N) :
    FactorsThrough N u (u * w) :=
  ⟨1, w⁻¹, N.one_mem, N.inv_mem hw, by group⟩

end FactorsThrough

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.peirceOneAdd_of_block
#audit_axioms GroupApproximation.MFQuotientUnits.peirceOneAdd_sum
#audit_axioms GroupApproximation.MFQuotientUnits.peirceOneAdd_of_left
#audit_axioms GroupApproximation.MFQuotientUnits.peirceOneAdd_of_right
#audit_axioms GroupApproximation.MFQuotientUnits.FactorsThrough.trans
