import GroupApproximation.GGT.KazhdanHypGQScheme
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# The symplectic generalized quadrangle `W(8)` in coordinates

This module defines the incidence geometry used by the large-table witness.
The coefficient field is `GaloisField 2 3`, so it has eight elements, and the
ambient vector space is `K^4`.  Points are projective one-spaces.  Lines are
two-dimensional subspaces on which the standard alternating form

```
  B(x,y) = x0*y2 + x1*y3 - x2*y0 - x3*y1
```

vanishes.  A point is incident with a line when it belongs to the associated
projective subspace.

These are the standard coordinates for the symplectic quadrangle `W(q)`; see
Payne--Thas, *Finite Generalized Quadrangles*, Section 3.2.1.  The proved
facts below are the first algebraic part of the generalized-quadrangle axioms:

* the field has cardinality eight;
* the ambient space has dimension four and `8^4` vectors;
* the projective point type has exactly `585 = (8+1)(8^2+1)` elements;
* the form is alternating, so every projective point is isotropic;
* two distinct points lie on at most one projective line, so in particular on
  at most one totally isotropic line.

The remaining coordinate count is the unique-projection theorem: for a point
outside a totally isotropic line, the restriction of `B(p,-)` to that line has
one-dimensional kernel.  Together with the cardinality of a projective line,
that theorem instantiates `GeneralizedQuadrangleCounts` at order eight.
-/

noncomputable section

namespace GroupApproximation
namespace KazhdanHyp
namespace SymplecticQuadrangle

open scoped LinearAlgebra.Projectivization

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- The field with `2^3 = 8` elements. -/
abbrev FieldEight := GaloisField 2 3

noncomputable instance fieldEightFintype : Fintype FieldEight :=
  Fintype.ofFinite FieldEight

/-- The four-dimensional symplectic vector space. -/
abbrev Vec := Fin 4 → FieldEight

/-- The `i`th standard coordinate vector. -/
def basisVector (i : Fin 4) : Vec := Pi.single i 1

/-- The standard symplectic bilinear form on `K^4`. -/
def form : LinearMap.BilinForm FieldEight Vec := by
  apply LinearMap.mk₂ FieldEight fun x y : Vec =>
    x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1
  · intro x x' y
    simp only [Pi.add_apply]
    ring
  · intro c x y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro x y y'
    simp only [Pi.add_apply]
    ring
  · intro c x y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem form_apply (x y : Vec) :
    form x y = x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1 := rfl

/-- The coordinate form is alternating over every coefficient field, including
characteristic two. -/
theorem form_isAlt : form.IsAlt := by
  intro x
  rw [form_apply]
  ring

/-- Orthogonality for the coordinate form is symmetric. -/
theorem form_eq_zero_comm (x y : Vec) : form x y = 0 ↔ form y x = 0 :=
  form_isAlt.eq_iff

/-- The Galois field used by `W(8)` has eight elements. -/
theorem fieldEight_card : Fintype.card FieldEight = 8 := by
  rw [← Nat.card_eq_fintype_card]
  simpa using GaloisField.card 2 3 (by norm_num : 3 ≠ 0)

/-- The ambient coordinate space has dimension four. -/
theorem vec_finrank : Module.finrank FieldEight Vec = 4 := by
  simpa [Vec] using Module.finrank_pi (R := FieldEight) (ι := Fin 4)

/-- The ambient coordinate space contains `8^4 = 4096` vectors. -/
theorem vec_card : Fintype.card Vec = 4096 := by
  rw [Fintype.card_fun, Fintype.card_fin, fieldEight_card]
  norm_num

/-- Points of the symplectic quadrangle are all projective one-spaces of
`K^4`; alternation makes every such point isotropic. -/
abbrev Point := Projectivization FieldEight Vec

noncomputable instance pointFintype : Fintype Point := Fintype.ofFinite Point
noncomputable instance pointDecidableEq : DecidableEq Point := Classical.decEq Point

/-- The projective three-space over the eight-element field has 585 points. -/
theorem point_card : Fintype.card Point = 585 := by
  rw [← Nat.card_eq_fintype_card]
  have h := Projectivization.card_of_finrank FieldEight Vec vec_finrank
  rw [show Nat.card FieldEight = 8 by
    simpa only [Nat.card_eq_fintype_card] using fieldEight_card] at h
  norm_num at h ⊢
  exact h

/-- Every projective point is isotropic for the alternating form. -/
theorem point_self_orthogonal (p : Point) : form p.rep p.rep = 0 :=
  form_isAlt.self_eq_zero p.rep

/-- A subspace is totally isotropic when the form vanishes on every pair of
its vectors. -/
def IsTotallyIsotropic (L : Submodule FieldEight Vec) : Prop :=
  ∀ x, x ∈ L → ∀ y, y ∈ L → form x y = 0

/-- Lines of `W(8)` are the two-dimensional totally isotropic subspaces. -/
abbrev Line := {L : Submodule FieldEight Vec //
  Module.finrank FieldEight L = 2 ∧ IsTotallyIsotropic L}

noncomputable instance submoduleFinite : Finite (Submodule FieldEight Vec) :=
  Finite.of_injective (fun L : Submodule FieldEight Vec => (L : Set Vec))
    SetLike.coe_injective

noncomputable instance lineFintype : Fintype Line := Fintype.ofFinite Line
noncomputable instance lineDecidableEq : DecidableEq Line := Classical.decEq Line

/-- Projective incidence between a one-space and a totally isotropic
two-space. -/
def Incident (p : Point) (L : Line) : Prop := p ∈ L.1.projectivization

noncomputable instance incidentDecidable : DecidableRel Incident :=
  fun _ _ => Classical.dec _

/-- Incidence puts a representative vector inside the underlying linear
subspace. -/
theorem rep_mem_of_incident {p : Point} {L : Line} (h : Incident p L) :
    p.rep ∈ L.1 := by
  have hle : p.submodule ≤ L.1 :=
    (Submodule.mem_projectivization_iff_submodule_le L.1 p).mp h
  apply hle
  rw [p.submodule_eq]
  exact Submodule.mem_span_singleton_self p.rep

/-- Two points on one symplectic line are orthogonal. -/
theorem orthogonal_of_incident {p q : Point} {L : Line}
    (hp : Incident p L) (hq : Incident q L) : form p.rep q.rep = 0 :=
  L.2.2 p.rep (rep_mem_of_incident hp) q.rep (rep_mem_of_incident hq)

/-- Two distinct projective points determine at most one two-dimensional
subspace.  This is the projective-line uniqueness theorem specialized to the
coordinate model. -/
theorem underlying_line_unique {p q : Point} (hpq : p ≠ q)
    (L M : Submodule FieldEight Vec)
    (hLdim : Module.finrank FieldEight L = 2)
    (hMdim : Module.finrank FieldEight M = 2)
    (hpL : p ∈ L.projectivization) (hqL : q ∈ L.projectivization)
    (hpM : p ∈ M.projectivization) (hqM : q ∈ M.projectivization) :
    L = M :=
  Projectivization.line_unique hpq L M hLdim hMdim hpL hqL hpM hqM

/-- **No four-cycle in the `W(8)` incidence graph.**  Two distinct points are
incident with at most one totally isotropic line. -/
theorem line_unique {p q : Point} (hpq : p ≠ q) {L M : Line}
    (hpL : Incident p L) (hqL : Incident q L)
    (hpM : Incident p M) (hqM : Incident q M) : L = M := by
  apply Subtype.ext
  exact underlying_line_unique hpq L.1 M.1 L.2.1 M.2.1 hpL hqL hpM hqM

/-! ## A concrete incident flag -/

private theorem basisVector_ne_zero (i : Fin 4) : basisVector i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simpa [basisVector, Pi.single_apply] using hi

/-- The first coordinate point. -/
def standardPoint : Point :=
  Projectivization.mk FieldEight (basisVector 0) (basisVector_ne_zero 0)

private theorem basis_zero_one_independent :
    LinearIndependent FieldEight ![basisVector 0, basisVector 1] := by
  let f : Fin 2 → Fin 4 := fun i => ⟨i.val, by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hv : (f i).val = (f j).val :=
      congrArg (fun z : Fin 4 => z.val) hij
    simpa [f] using hv
  have h := (Pi.basisFun FieldEight (Fin 4)).linearIndependent.comp
    f hf
  rw [show ![basisVector 0, basisVector 1] =
      ((Pi.basisFun FieldEight (Fin 4) : Fin 4 → Vec) ∘ f) by
    funext i
    fin_cases i <;> simp [Function.comp_apply, f, basisVector, Pi.basisFun_apply]]
  exact h

private theorem standardPlane_finrank :
    Module.finrank FieldEight
      (Submodule.span FieldEight {basisVector 0, basisVector 1}) = 2 := by
  rw [← Matrix.range_cons_cons_empty (basisVector 0) (basisVector 1) ![]]
  simpa using finrank_span_eq_card basis_zero_one_independent

private theorem standardPlane_isotropic :
    IsTotallyIsotropic (Submodule.span FieldEight {basisVector 0, basisVector 1}) := by
  intro x hx y hy
  rw [Submodule.mem_span_pair] at hx hy
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  simp [form_apply, basisVector, Pi.single_apply]

/-- The totally isotropic plane spanned by the first two coordinate vectors. -/
def standardLine : Line :=
  ⟨Submodule.span FieldEight {basisVector 0, basisVector 1},
    standardPlane_finrank, standardPlane_isotropic⟩

/-- The concrete coordinate point lies on the concrete isotropic line, so the
incidence type is nonempty. -/
theorem standardPoint_incident_standardLine : Incident standardPoint standardLine := by
  unfold Incident standardPoint standardLine
  rw [Submodule.mk_mem_projectivization_iff]
  exact Submodule.mem_span_of_mem (Set.mem_insert _ _)

/-- Model test: the algebraic incidence relation is nonempty and its first
flag satisfies the orthogonality equation. -/
theorem standardFlagModel :
    Incident standardPoint standardLine ∧
      form standardPoint.rep standardPoint.rep = 0 :=
  ⟨standardPoint_incident_standardLine, point_self_orthogonal standardPoint⟩

end SymplecticQuadrangle
end KazhdanHyp
end GroupApproximation
