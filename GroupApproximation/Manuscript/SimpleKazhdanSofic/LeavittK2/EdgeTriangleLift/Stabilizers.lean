import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Weyl.Basic
import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Meta.AxiomGuard

/-!
# Edge and triangle lifts I: column stabilizers in `GL_4(R)` (lane sk-leavitt-13)

Khanh (arXiv:2609.08428), proof of Theorem 5.1.  The corpus pads along `Fin.castSucc`, so the
base vertex is `e₃` and the base edge is `(e₃, e₂)` (see `LeavittK2.Criterion`).  The edge group
of Brown's presentation is `K = J ∩ Stab(e₂) = {g | g e₃ = e₃, g e₂ = e₂}`.

This file works over an arbitrary ring `R`.

* `columnFixer c`: the subgroup `{g | g e_c = e_c}`, i.e. column `c` of `g` is the standard one.
* `edgeStab R = columnFixer 3 ⊓ columnFixer 2`, the group `K`.
* `edgeGens R`: the elementary matrices `1 + E_{pq}(c)` with `q < 2`.  They generate a subgroup
  of `edgeStab R` (`closure_edgeGens_le`); the converse is `EdgeGeneration`.
* `mulVec_single_iff`: `g e_c = e_c` in `Pi.single` form, the form used by `Criterion.vertexStab`.
* `projection_weyl_three_two`: when `2 = 0`, `w₃₂ = x₃₂(1) x₂₃(1) x₃₂(1)` maps to the corpus
  Weyl monomial `ElementaryWeyl.weylUnit 3 2`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R]

/-- `2 ≤ 4`, for padding `Fin 2` into `Fin 4`. -/
theorem two_le_four : 2 ≤ 4 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.two_le_four

/-- **The stabilizer of the standard basis vector `e_c`**: column `c` is the identity column. -/
def columnFixer (c : Fin 4) : Subgroup (Matrix (Fin 4) (Fin 4) R)ˣ where
  carrier := {g | ∀ p : Fin 4,
    (g : Matrix (Fin 4) (Fin 4) R) p c = (1 : Matrix (Fin 4) (Fin 4) R) p c}
  mul_mem' {a b} ha hb := by
    have ha' : ∀ p : Fin 4,
        (a : Matrix (Fin 4) (Fin 4) R) p c = (1 : Matrix (Fin 4) (Fin 4) R) p c := ha
    have hb' : ∀ p : Fin 4,
        (b : Matrix (Fin 4) (Fin 4) R) p c = (1 : Matrix (Fin 4) (Fin 4) R) p c := hb
    show ∀ p : Fin 4, ((a * b : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) p c =
      (1 : Matrix (Fin 4) (Fin 4) R) p c
    intro p
    calc ((a * b : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) p c
        = ∑ r : Fin 4, (a : Matrix (Fin 4) (Fin 4) R) p r * (b : Matrix (Fin 4) (Fin 4) R) r c := by
          rw [Units.val_mul, Matrix.mul_apply]
      _ = ∑ r : Fin 4, (a : Matrix (Fin 4) (Fin 4) R) p r * (1 : Matrix (Fin 4) (Fin 4) R) r c :=
          Finset.sum_congr rfl fun r _ => by rw [hb' r]
      _ = ((a : Matrix (Fin 4) (Fin 4) R) * (1 : Matrix (Fin 4) (Fin 4) R)) p c :=
          Matrix.mul_apply.symm
      _ = (1 : Matrix (Fin 4) (Fin 4) R) p c := by rw [Matrix.mul_one, ha' p]
  one_mem' := by
    show ∀ p : Fin 4, ((1 : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) p c =
      (1 : Matrix (Fin 4) (Fin 4) R) p c
    intro p
    rfl
  inv_mem' {a} ha := by
    have ha' : ∀ p : Fin 4,
        (a : Matrix (Fin 4) (Fin 4) R) p c = (1 : Matrix (Fin 4) (Fin 4) R) p c := ha
    show ∀ p : Fin 4, ((a⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) p c =
      (1 : Matrix (Fin 4) (Fin 4) R) p c
    intro p
    calc ((a⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) p c
        = (((a⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) *
            (1 : Matrix (Fin 4) (Fin 4) R)) p c := by rw [Matrix.mul_one]
      _ = ∑ r : Fin 4, ((a⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) p r *
            (1 : Matrix (Fin 4) (Fin 4) R) r c := Matrix.mul_apply
      _ = ∑ r : Fin 4, ((a⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) p r *
            (a : Matrix (Fin 4) (Fin 4) R) r c :=
          Finset.sum_congr rfl fun r _ => by rw [ha' r]
      _ = (((a⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) *
            (a : Matrix (Fin 4) (Fin 4) R)) p c := Matrix.mul_apply.symm
      _ = (1 : Matrix (Fin 4) (Fin 4) R) p c := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.columnFixer

theorem mem_columnFixer {c : Fin 4} {g : (Matrix (Fin 4) (Fin 4) R)ˣ} :
    g ∈ columnFixer c ↔
      ∀ p : Fin 4, (g : Matrix (Fin 4) (Fin 4) R) p c = (1 : Matrix (Fin 4) (Fin 4) R) p c :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.mem_columnFixer

/-- **The edge group `K = Stab(e₃) ∩ Stab(e₂)`.** -/
def edgeStab (R : Type*) [Ring R] : Subgroup (Matrix (Fin 4) (Fin 4) R)ˣ :=
  columnFixer 3 ⊓ columnFixer 2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.edgeStab

theorem mem_edgeStab {g : (Matrix (Fin 4) (Fin 4) R)ˣ} :
    g ∈ edgeStab R ↔ g ∈ columnFixer 3 ∧ g ∈ columnFixer 2 :=
  Subgroup.mem_inf

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.mem_edgeStab

/-- `1 + E_{pq}(a)` fixes `e_c` when `q ≠ c`. -/
theorem elementaryUnit_mem_columnFixer {c p q : Fin 4} (hpq : p ≠ q) (hq : q ≠ c) (a : R) :
    elementaryUnit p q hpq a ∈ columnFixer c := by
  rw [mem_columnFixer]
  intro r
  show (1 + Matrix.single p q a) r c = (1 : Matrix (Fin 4) (Fin 4) R) r c
  rw [Matrix.add_apply, Matrix.single_apply_of_col_ne _ _ hq _, add_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.elementaryUnit_mem_columnFixer

/-- The generators of `K`: elementary matrices `1 + E_{pq}(c)` with `q ∈ {0, 1}`. -/
def edgeGens (R : Type*) [Ring R] : Set (Matrix (Fin 4) (Fin 4) R)ˣ :=
  {z | ∃ (p q : Fin 4) (h : p ≠ q) (c : R), q.val < 2 ∧ elementaryUnit p q h c = z}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.edgeGens

/-- A column index `q < 2` differs from `3`. -/
theorem ne_three_of_lt_two {q : Fin 4} (hq : q.val < 2) : q ≠ 3 := by
  rintro rfl
  exact absurd hq (by decide)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.ne_three_of_lt_two

/-- A column index `q < 2` differs from `2`. -/
theorem ne_two_of_lt_two {q : Fin 4} (hq : q.val < 2) : q ≠ 2 := by
  rintro rfl
  exact absurd hq (by decide)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.ne_two_of_lt_two

/-- The generators lie in `K`. -/
theorem closure_edgeGens_le : Subgroup.closure (edgeGens R) ≤ edgeStab R := by
  rw [Subgroup.closure_le]
  rintro z ⟨p, q, hpq, c, hq, rfl⟩
  exact mem_edgeStab.mpr ⟨elementaryUnit_mem_columnFixer hpq (ne_three_of_lt_two hq) c,
    elementaryUnit_mem_columnFixer hpq (ne_two_of_lt_two hq) c⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.closure_edgeGens_le

/-- `M e_c = e_c`, written with `Pi.single`, says column `c` of `M` is the identity column. -/
theorem mulVec_single_iff (M : Matrix (Fin 4) (Fin 4) R) (c : Fin 4) :
    M *ᵥ Pi.single c 1 = Pi.single c 1 ↔
      ∀ p : Fin 4, M p c = (1 : Matrix (Fin 4) (Fin 4) R) p c := by
  rw [Matrix.mulVec_single_one]
  constructor
  · intro h p
    rw [← Matrix.col_apply M c p, h, Pi.single_apply, Matrix.one_apply]
  · intro h
    funext p
    rw [Matrix.col_apply, h p, Pi.single_apply, Matrix.one_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.mulVec_single_iff

/-- **The image of `w₃₂`** in characteristic two is the corpus Weyl monomial
`x₃₂(1) x₂₃(-1) x₃₂(1)`. -/
theorem projection_weyl_three_two (h2 : (2 : R) = 0) (h32 : (3 : Fin 4) ≠ 2) :
    ((projection (weyl (R := R) (3 : Fin 4) 2 h32) : elementaryGroup (Fin 4) R) :
        (Matrix (Fin 4) (Fin 4) R)ˣ) = ElementaryWeyl.weylUnit (3 : Fin 4) 2 h32 := by
  simp only [weyl, map_mul, Subgroup.coe_mul, projection_x, elementaryRoot_val]
  rw [ElementaryWeyl.weylUnit, WeylCalc.neg_self_of_two_eq_zero h2]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.projection_weyl_three_two

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift
