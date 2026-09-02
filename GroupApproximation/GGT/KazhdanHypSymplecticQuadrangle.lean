import GroupApproximation.GGT.KazhdanHypGQScheme
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dual.Lemmas
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

/-- The standard coordinate form separates vectors in the left argument. -/
theorem form_separatingLeft : form.SeparatingLeft := by
  intro x hx
  funext i
  fin_cases i
  · have h := hx (basisVector 2)
    simpa [form_apply, basisVector, Pi.single_apply] using h
  · have h := hx (basisVector 3)
    simpa [form_apply, basisVector, Pi.single_apply] using h
  · have h := hx (basisVector 0)
    simpa [form_apply, basisVector, Pi.single_apply] using h
  · have h := hx (basisVector 1)
    simpa [form_apply, basisVector, Pi.single_apply] using h

/-- The standard symplectic form is nondegenerate. -/
theorem form_nondegenerate : form.Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft form_separatingLeft

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

/-! ## Unique projection to an isotropic line -/

/-- A totally isotropic line lies in its symplectic orthogonal complement. -/
theorem line_le_orthogonal (L : Line) : L.1 ≤ form.orthogonal L.1 := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  exact L.2.2 y hy x hx

/-- A two-dimensional totally isotropic subspace is Lagrangian: its
orthogonal complement is itself. -/
theorem line_orthogonal_eq (L : Line) : form.orthogonal L.1 = L.1 := by
  apply (Submodule.eq_of_le_of_finrank_eq (line_le_orthogonal L) ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate, vec_finrank,
    L.2.1]

/-- Restrict the functional `B(p,-)` to a symplectic line. -/
def lineFunctional (p : Point) (L : Line) : L.1 →ₗ[FieldEight] FieldEight :=
  (form p.rep).comp L.1.subtype

/-- If `p` is outside `L`, the restricted functional `B(p,-)` is nonzero. -/
theorem lineFunctional_ne_zero {p : Point} {L : Line} (hout : ¬ Incident p L) :
    lineFunctional p L ≠ 0 := by
  intro hzero
  have hpOrth : p.rep ∈ form.orthogonal L.1 := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have happ := LinearMap.congr_fun hzero ⟨y, hy⟩
    have hpy : form p.rep y = 0 := by
      simpa [lineFunctional] using happ
    exact (form_eq_zero_comm p.rep y).mp hpy
  apply hout
  rw [Incident, Submodule.mem_projectivization_iff_submodule_le]
  rw [p.submodule_eq, ← line_orthogonal_eq L]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hpOrth)

/-- The kernel of the restricted functional, transported back into the
ambient four-space. -/
def projectionSubmodule (p : Point) (L : Line) : Submodule FieldEight Vec :=
  (LinearMap.ker (lineFunctional p L)).map L.1.subtype

/-- For an outside point, the projection kernel is one-dimensional. -/
theorem projectionSubmodule_finrank {p : Point} {L : Line}
    (hout : ¬ Incident p L) :
    Module.finrank FieldEight (projectionSubmodule p L) = 1 := by
  rw [projectionSubmodule, Submodule.finrank_map_subtype_eq]
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero
    (lineFunctional_ne_zero hout)
  have hdim : Module.finrank FieldEight L.1 = 2 := L.2.1
  omega

/-- The unique point of `L` orthogonal to an outside point `p`. -/
def projectedPoint (p : Point) (L : Line) (hout : ¬ Incident p L) : Point :=
  Projectivization.mk'' (projectionSubmodule p L)
    (projectionSubmodule_finrank hout)

/-- The projected point belongs to the given isotropic line. -/
theorem projectedPoint_incident (p : Point) (L : Line) (hout : ¬ Incident p L) :
    Incident (projectedPoint p L hout) L := by
  rw [Incident, Submodule.mem_projectivization_iff_submodule_le]
  change (Projectivization.mk'' (projectionSubmodule p L)
    (projectionSubmodule_finrank hout)).submodule ≤ L.1
  rw [Projectivization.submodule_mk'']
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact y.2

/-- The projected point is orthogonal to the outside point. -/
theorem projectedPoint_orthogonal (p : Point) (L : Line)
    (hout : ¬ Incident p L) :
    form p.rep (projectedPoint p L hout).rep = 0 := by
  have hmem : (projectedPoint p L hout).rep ∈ projectionSubmodule p L := by
    have hm : (projectedPoint p L hout).rep ∈
        (projectedPoint p L hout).submodule := by
      rw [(projectedPoint p L hout).submodule_eq]
      exact Submodule.mem_span_singleton_self _
    rw [show (projectedPoint p L hout).submodule = projectionSubmodule p L by
      exact Projectivization.submodule_mk'' _ _] at hm
    exact hm
  obtain ⟨y, hy, heq⟩ := hmem
  have hyzero : lineFunctional p L y = 0 := by
    exact LinearMap.mem_ker.mp hy
  rw [← heq]
  simpa [lineFunctional] using hyzero

/-- Any point of `L` orthogonal to `p` spans the projection kernel. -/
theorem submodule_eq_projectionSubmodule {p q : Point} {L : Line}
    (hout : ¬ Incident p L) (hqL : Incident q L)
    (hpq : form p.rep q.rep = 0) :
    q.submodule = projectionSubmodule p L := by
  have hqmem : q.rep ∈ L.1 := rep_mem_of_incident hqL
  have hqker : (⟨q.rep, hqmem⟩ : L.1) ∈ LinearMap.ker (lineFunctional p L) := by
    rw [LinearMap.mem_ker]
    simpa [lineFunctional] using hpq
  have hle : q.submodule ≤ projectionSubmodule p L := by
    rw [q.submodule_eq]
    apply Submodule.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact ⟨⟨q.rep, hqmem⟩, hqker, rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [q.finrank_submodule, projectionSubmodule_finrank hout]

/-- **The generalized-quadrangle projection axiom for `W(8)`.**  Given a
point outside an isotropic line, there is exactly one point on that line
orthogonal (so collinear) to it. -/
theorem existsUnique_incident_orthogonal (p : Point) (L : Line)
    (hout : ¬ Incident p L) :
    ∃! q : Point, Incident q L ∧ form p.rep q.rep = 0 := by
  refine ⟨projectedPoint p L hout,
    ⟨projectedPoint_incident p L hout,
      projectedPoint_orthogonal p L hout⟩, ?_⟩
  intro q hq
  apply Projectivization.submodule_injective
  rw [submodule_eq_projectionSubmodule hout hq.1 hq.2]
  exact (Projectivization.submodule_mk'' (projectionSubmodule p L)
    (projectionSubmodule_finrank hout)).symm

/-! ## The nine points on each isotropic line -/

/-- Embed the projectivization of a submodule into the ambient projective
space. -/
def submodulePoint (L : Submodule FieldEight Vec)
    (p : Projectivization FieldEight L) : Point :=
  Projectivization.map L.subtype L.injective_subtype p

/-- A projective point of a submodule belongs to the corresponding ambient
projective subspace. -/
theorem submodulePoint_mem (L : Submodule FieldEight Vec)
    (p : Projectivization FieldEight L) :
    submodulePoint L p ∈ L.projectivization := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [submodulePoint, Projectivization.map_mk,
        Submodule.mk_mem_projectivization_iff]
      exact v.2

/-- Projectivizing a submodule is equivalent to taking the subtype of
ambient projective points which lie in it. -/
def submodulePointEquiv (L : Submodule FieldEight Vec) :
    Projectivization FieldEight L ≃ {p : Point // p ∈ L.projectivization} := by
  let f : Projectivization FieldEight L →
      {p : Point // p ∈ L.projectivization} :=
    fun p => ⟨submodulePoint L p, submodulePoint_mem L p⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply Projectivization.map_injective L.subtype L.injective_subtype
    exact congrArg Subtype.val hpq
  · intro q
    have hrep : q.1.rep ∈ L := by
      have hle : q.1.submodule ≤ L :=
        (Submodule.mem_projectivization_iff_submodule_le L q.1).mp q.2
      apply hle
      rw [q.1.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    let v : L := ⟨q.1.rep, hrep⟩
    have hv : v ≠ 0 := by
      intro hz
      exact q.1.rep_nonzero (congrArg Subtype.val hz)
    refine ⟨Projectivization.mk FieldEight v hv, ?_⟩
    apply Subtype.ext
    change Projectivization.map L.subtype L.injective_subtype
      (Projectivization.mk FieldEight v hv) = q.1
    rw [Projectivization.map_mk]
    exact q.1.mk_rep

/-- Every isotropic line contains exactly `8+1=9` projective points. -/
theorem incident_point_card (L : Line) :
    Fintype.card {p : Point // Incident p L} = 9 := by
  classical
  letI : Fintype (Projectivization FieldEight L.1) := Fintype.ofFinite _
  calc
    Fintype.card {p : Point // Incident p L} =
        Fintype.card (Projectivization FieldEight L.1) := by
      exact Fintype.card_congr (submodulePointEquiv L.1).symm
    _ = 9 := by
      rw [← Nat.card_eq_fintype_card]
      have h := Projectivization.card_of_finrank FieldEight L.1 L.2.1
      rw [show Nat.card FieldEight = 8 by
        simpa only [Nat.card_eq_fintype_card] using fieldEight_card] at h
      norm_num at h ⊢
      exact h

/-- The natural incidence row sum on the line side is nine. -/
theorem incident_line_degree (L : Line) :
    ∑ p, incidenceWeight Incident p L = 9 := by
  classical
  calc
    (∑ p, incidenceWeight Incident p L) =
        (Finset.univ.filter fun p => Incident p L).card := by
      simp [incidenceWeight]
    _ = Fintype.card {p : Point // Incident p L} :=
      (Fintype.card_subtype _).symm
    _ = 9 := incident_point_card L

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
