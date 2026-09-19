import GroupApproximation.Sofic.GreendlingerOneRelator

/-!
# Expressions as products of conjugates, and the base of the descent

`GreendlingerOneRelator` proves the Greendlinger conclusion for a word spelling a
*single* conjugate of a symmetrized relator.  The layer still open is the descent
from a **minimal expression** with several conjugate factors down to that case.
This file supplies the object that descent is an induction over, and proves the
base of the induction.

## The object

`IsConjProduct R n g` says `g` is a product of `n` conjugates of symmetrized
relators.  `mem_normalClosure_iff` identifies the normal closure of the relators
with the elements admitting such an expression for some `n`: the family of those
elements is a normal subgroup (closed under products by concatenating
expressions, under inverses because `symmetrization` is closed under `invRev`,
and under conjugation because conjugating a conjugate is a conjugate), it
contains the relators, and each of its members is visibly in the normal closure.

So "minimal expression" is now a statement about a natural number, and the
remaining obligation of the gate is an induction on it.

## The base

* `n = 0` is impossible for a nonempty reduced word: it would say `mk w = 1`,
  and reduced words spelling `1` are empty (`not_isConjProduct_zero`);
* `n = 1` is exactly the single-conjugate case, which
  `greendlinger_of_isConj` already settles
  (`greendlinger_of_isConjProduct_one`).

What is left is `n ≥ 2` with `n` minimal, which is where the `C'(1/6)` piece
bound enters and where classical treatments reach for van Kampen diagrams.

Unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Products of conjugates -/

/-- `g` is a product of `n` conjugates of symmetrized relators. -/
def IsConjProduct (R : Set (List (α × Bool))) : ℕ → FreeGroup α → Prop
  | 0, g => g = 1
  | n + 1, g => ∃ (c : FreeGroup α) (s : List (α × Bool)),
      s ∈ symmetrization R ∧ ∃ h : FreeGroup α,
        IsConjProduct R n h ∧ g = c * FreeGroup.mk s * c⁻¹ * h

theorem isConjProduct_one_of_mem {R : Set (List (α × Bool))}
    {s : List (α × Bool)} (hs : s ∈ symmetrization R) (c : FreeGroup α) :
    IsConjProduct R 1 (c * FreeGroup.mk s * c⁻¹) :=
  ⟨c, s, hs, 1, rfl, by group⟩

/-- Expressions concatenate. -/
theorem IsConjProduct.mul {R : Set (List (α × Bool))} :
    ∀ {m n : ℕ} {g h : FreeGroup α}, IsConjProduct R m g →
      IsConjProduct R n h → IsConjProduct R (m + n) (g * h) := by
  intro m
  induction m with
  | zero =>
      intro n g h hg hh
      have hg1 : g = 1 := hg
      subst hg1
      simpa using hh
  | succ m ih =>
      intro n g h hg hh
      obtain ⟨c, s, hs, g', hg', rfl⟩ := hg
      have hidx : m + 1 + n = m + n + 1 := by omega
      rw [hidx]
      refine ⟨c, s, hs, g' * h, ih hg' hh, ?_⟩
      group

/-- Conjugating an expression conjugates each factor. -/
theorem IsConjProduct.conj {R : Set (List (α × Bool))} :
    ∀ {n : ℕ} {g : FreeGroup α}, IsConjProduct R n g →
      ∀ d : FreeGroup α, IsConjProduct R n (d * g * d⁻¹) := by
  intro n
  induction n with
  | zero =>
      intro g hg d
      have hg1 : g = 1 := hg
      subst hg1
      show d * 1 * d⁻¹ = 1
      group
  | succ n ih =>
      intro g hg d
      obtain ⟨c, s, hs, h, hh, rfl⟩ := hg
      refine ⟨d * c, s, hs, d * h * d⁻¹, ih hh d, ?_⟩
      group

/-- Inverting an expression inverts each factor, and the inverse of a
symmetrized relator is again one. -/
theorem IsConjProduct.inv {R : Set (List (α × Bool))} :
    ∀ {n : ℕ} {g : FreeGroup α}, IsConjProduct R n g →
      IsConjProduct R n g⁻¹ := by
  intro n
  induction n with
  | zero =>
      intro g hg
      have hg1 : g = 1 := hg
      subst hg1
      show (1 : FreeGroup α)⁻¹ = 1
      group
  | succ n ih =>
      intro g hg
      obtain ⟨c, s, hs, h, hh, rfl⟩ := hg
      have hstep : IsConjProduct R 1
          (c * FreeGroup.mk (FreeGroup.invRev s) * c⁻¹) :=
        isConjProduct_one_of_mem (invRev_mem_symmetrization hs) c
      have hprod := (ih hh).mul hstep
      have heq : (c * FreeGroup.mk s * c⁻¹ * h)⁻¹
          = h⁻¹ * (c * FreeGroup.mk (FreeGroup.invRev s) * c⁻¹) := by
        rw [← FreeGroup.inv_mk]
        group
      rw [heq]
      exact hprod

/-! ## The normal closure -/

/-- The elements admitting a conjugate-product expression. -/
def conjProductSubgroup (R : Set (List (α × Bool))) : Subgroup (FreeGroup α) where
  carrier := {g | ∃ n, IsConjProduct R n g}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := fun ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, hm.mul hn⟩
  inv_mem' := fun ⟨n, hn⟩ => ⟨n, hn.inv⟩

instance conjProductSubgroup_normal (R : Set (List (α × Bool))) :
    (conjProductSubgroup R).Normal :=
  ⟨fun _g ⟨n, hn⟩ d => ⟨n, hn.conj d⟩⟩

theorem mem_normalClosure_of_isConjProduct {R : Set (List (α × Bool))} :
    ∀ {n : ℕ} {g : FreeGroup α}, IsConjProduct R n g →
      g ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
  intro n
  induction n with
  | zero =>
      intro g hg
      have hg1 : g = 1 := hg
      subst hg1
      exact one_mem _
  | succ n ih =>
      intro g hg
      obtain ⟨c, s, hs, h, hh, rfl⟩ := hg
      refine mul_mem ?_ (ih hh)
      have hsmem : FreeGroup.mk s
          ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
        rw [← normalClosure_symmetrization R]
        exact Subgroup.subset_normalClosure ⟨s, hs, rfl⟩
      exact Subgroup.normalClosure_normal.conj_mem _ hsmem c

/-- **The normal closure is exactly the elements with a conjugate-product
expression.**  This is what makes "a minimal expression" a statement about a
natural number, and so makes the remaining layer of the gate an induction. -/
theorem mem_normalClosure_iff (R : Set (List (α × Bool))) (g : FreeGroup α) :
    g ∈ Subgroup.normalClosure (FreeGroup.mk '' R) ↔ ∃ n, IsConjProduct R n g := by
  constructor
  · intro hg
    have hsub : FreeGroup.mk '' R ⊆ (conjProductSubgroup R : Set (FreeGroup α)) := by
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨1, isConjProduct_one_of_mem (subset_symmetrization R hr) 1⟩
    exact Subgroup.normalClosure_le_normal hsub hg
  · rintro ⟨n, hn⟩
    exact mem_normalClosure_of_isConjProduct hn

/-! ## The base of the descent -/

/-- A nonempty reduced word never spells the empty product. -/
theorem not_isConjProduct_zero {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ []) :
    ¬ IsConjProduct R 0 (FreeGroup.mk w) := by
  intro h
  have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
    have hone : FreeGroup.mk w = 1 := h
    rw [hone, FreeGroup.one_eq_mk]
  have h2 := FreeGroup.reduce.sound h1
  rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
  exact hwne h2

/-- **The base of the descent.**  An expression with a single conjugate factor
already gives the Greendlinger conclusion, by the one-relator case. -/
theorem greendlinger_of_isConjProduct_one {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (h : IsConjProduct R 1 (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧ t.length < 2 * u.length := by
  obtain ⟨c, s, hs, h', hh', heq⟩ := h
  have hh1 : h' = 1 := hh'
  subst hh1
  refine greendlinger_of_isConj hR hRne hs hw ?_
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [heq]
  group

end SmallCancellationRouter
end GroupApproximation
