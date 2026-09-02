import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangle

/-!
# Incidence counts in the symplectic quadrangle W(8)

This module derives the missing point-side regularity of the coordinate
symplectic quadrangle.  For a projective point `p`, its orthogonal hyperplane
has dimension three and so contains 73 projective points.  Removing `p`
leaves 72 points.  Counting the same set as a point on a line through `p`
and one of the other eight points of that line gives

```text
  8 * numberOfLinesThrough(p) = 72.
```

Thus every point lies on nine isotropic lines.  Double-counting incident
point-line flags then gives 585 lines.  These are the standard finite counts
for `W(8)`; see Payne--Thas, *Finite Generalized Quadrangles*, Section 3.2.1.
-/

noncomputable section

namespace GroupApproximation
namespace KazhdanHyp
namespace SymplecticQuadrangle

open scoped BigOperators LinearAlgebra.Projectivization

set_option linter.unusedSimpArgs false

/-! ## The projective orthogonal hyperplane -/

/-- The hyperplane orthogonal to a projective point representative. -/
def pointOrthogonalSubmodule (p : Point) : Submodule FieldEight Vec :=
  LinearMap.ker (form p.rep)

/-- The functional defined by a nonzero projective representative is
nonzero, by nondegeneracy of the symplectic form. -/
theorem pointFunctional_ne_zero (p : Point) : form p.rep ≠ 0 := by
  intro hzero
  apply p.rep_nonzero
  apply form_separatingLeft p.rep
  intro y
  exact LinearMap.congr_fun hzero y

/-- A point orthogonal hyperplane has dimension three. -/
theorem pointOrthogonalSubmodule_finrank (p : Point) :
    Module.finrank FieldEight (pointOrthogonalSubmodule p) = 3 := by
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero
    (pointFunctional_ne_zero p)
  change Module.finrank FieldEight (LinearMap.ker (form p.rep)) = 3
  rw [vec_finrank] at hker
  omega

/-- Membership in the projectivized orthogonal hyperplane is the coordinate
orthogonality equation. -/
theorem mem_pointOrthogonal_projectivization_iff (p q : Point) :
    q ∈ (pointOrthogonalSubmodule p).projectivization ↔
      form p.rep q.rep = 0 := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  constructor
  · intro hle
    have hmem : q.rep ∈ pointOrthogonalSubmodule p := by
      apply hle
      rw [q.submodule_eq]
      exact Submodule.mem_span_singleton_self q.rep
    exact LinearMap.mem_ker.mp hmem
  · intro horth
    rw [q.submodule_eq]
    apply Submodule.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr horth

/-- Projective points in the orthogonal hyperplane are exactly the points
orthogonal to `p`. -/
def orthogonalPointEquiv (p : Point) :
    Projectivization FieldEight (pointOrthogonalSubmodule p) ≃
      {q : Point // form p.rep q.rep = 0} :=
  (submodulePointEquiv (pointOrthogonalSubmodule p)).trans
    (Equiv.subtypeEquivProp (by
      funext q
      apply propext
      exact mem_pointOrthogonal_projectivization_iff p q))

noncomputable instance orthogonalPointSubtypeFintype (p : Point) :
    Fintype {q : Point // form p.rep q.rep = 0} :=
  Fintype.ofFinite _

/-- Exactly 73 projective points are orthogonal to a fixed point. -/
theorem orthogonalPoint_card (p : Point) :
    Fintype.card {q : Point // form p.rep q.rep = 0} = 73 := by
  classical
  letI : Fintype
      (Projectivization FieldEight (pointOrthogonalSubmodule p)) :=
    Fintype.ofFinite _
  calc
    Fintype.card {q : Point // form p.rep q.rep = 0} =
        Fintype.card
          (Projectivization FieldEight (pointOrthogonalSubmodule p)) :=
      Fintype.card_congr (orthogonalPointEquiv p).symm
    _ = 73 := by
      rw [← Nat.card_eq_fintype_card]
      have h := Projectivization.card_of_finrank FieldEight
        (pointOrthogonalSubmodule p) (pointOrthogonalSubmodule_finrank p)
      rw [show Nat.card FieldEight = 8 by
        simpa only [Nat.card_eq_fintype_card] using fieldEight_card] at h
      norm_num at h ⊢
      exact h

/-! ## Removing the base point and counting flags -/

/-- Orthogonal projective points other than the chosen point. -/
abbrev OrthogonalOther (p : Point) :=
  {q : Point // q ≠ p ∧ form p.rep q.rep = 0}

noncomputable instance orthogonalOtherFintype (p : Point) :
    Fintype (OrthogonalOther p) :=
  Fintype.ofFinite _

/-- Reassociate the two predicates so `Set.card_ne_eq` applies inside the
73-element orthogonal-point subtype. -/
def orthogonalOtherEquiv (p : Point) :
    OrthogonalOther p ≃
      {q : {r : Point // form p.rep r.rep = 0} //
        q ≠ ⟨p, point_self_orthogonal p⟩} where
  toFun q := ⟨⟨q.1, q.2.2⟩, by
    intro h
    apply q.2.1
    exact congrArg (fun z : {r : Point // form p.rep r.rep = 0} ↦ z.1) h⟩
  invFun q := ⟨q.1.1, by
    constructor
    · intro h
      apply q.2
      apply Subtype.ext
      exact h
    · exact q.1.2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

/-- There are 72 orthogonal points distinct from `p`. -/
theorem orthogonalOther_card (p : Point) :
    Fintype.card (OrthogonalOther p) = 72 := by
  classical
  calc
    Fintype.card (OrthogonalOther p) =
        Fintype.card
          {q : {r : Point // form p.rep r.rep = 0} //
            q ≠ ⟨p, point_self_orthogonal p⟩} :=
      Fintype.card_congr (orthogonalOtherEquiv p)
    _ = Fintype.card {r : Point // form p.rep r.rep = 0} - 1 :=
      Set.card_ne_eq
        (⟨p, point_self_orthogonal p⟩ :
          {r : Point // form p.rep r.rep = 0})
    _ = 72 := by rw [orthogonalPoint_card]

/-- Isotropic lines through a fixed point. -/
abbrev PointLine (p : Point) := {L : Line // Incident p L}

noncomputable instance pointLineFintype (p : Point) : Fintype (PointLine p) :=
  Fintype.ofFinite _

/-- Points on a flagged line other than the fixed point. -/
abbrev OtherPointOn (p : Point) (L : PointLine p) :=
  {q : Point // Incident q L.1 ∧ q ≠ p}

noncomputable instance otherPointOnFintype (p : Point) (L : PointLine p) :
    Fintype (OtherPointOn p L) :=
  Fintype.ofFinite _

/-- A flagged line through `p`, together with another point on that line. -/
abbrev PointLineOtherFlag (p : Point) :=
  Σ L : PointLine p, OtherPointOn p L

/-- Removing one specified incident point from a nine-point line leaves
eight points. -/
theorem otherPointOn_card (p : Point) (L : PointLine p) :
    Fintype.card (OtherPointOn p L) = 8 := by
  classical
  let e : OtherPointOn p L ≃
      {q : {r : Point // Incident r L.1} // q ≠ ⟨p, L.2⟩} :=
    { toFun := fun q ↦ ⟨⟨q.1, q.2.1⟩, by
        intro h
        apply q.2.2
        exact congrArg (fun z : {r : Point // Incident r L.1} ↦ z.1) h⟩
      invFun := fun q ↦ ⟨q.1.1, q.1.2, by
        intro h
        apply q.2
        apply Subtype.ext
        exact h⟩
      left_inv := by intro q; apply Subtype.ext; rfl
      right_inv := by intro q; apply Subtype.ext; rfl }
  calc
    Fintype.card (OtherPointOn p L) =
        Fintype.card {q : {r : Point // Incident r L.1} // q ≠ ⟨p, L.2⟩} :=
      Fintype.card_congr e
    _ = Fintype.card {r : Point // Incident r L.1} - 1 :=
      Set.card_ne_eq (⟨p, L.2⟩ : {r : Point // Incident r L.1})
    _ = 8 := by rw [incident_point_card]

/-- A line and another point on it determine an orthogonal point distinct
from the fixed point. -/
def pointLineOtherToOrthogonalOther (p : Point) :
    PointLineOtherFlag p → OrthogonalOther p :=
  fun x ↦ ⟨x.2.1, x.2.2.2,
    orthogonal_of_incident x.1.2 x.2.2.1⟩

/-- The flag-to-orthogonal-point map is injective because two distinct
projective points determine at most one isotropic line. -/
theorem pointLineOtherToOrthogonalOther_injective (p : Point) :
    Function.Injective (pointLineOtherToOrthogonalOther p) := by
  intro x y hxy
  have hpoint : x.2.1 = y.2.1 :=
    congrArg (fun q : OrthogonalOther p ↦ q.1) hxy
  have hpne : p ≠ x.2.1 := Ne.symm x.2.2.2
  have hline : x.1.1 = y.1.1 := by
    apply line_unique hpne x.1.2 x.2.2.1 y.1.2
    rw [hpoint]
    exact y.2.2.1
  have hflag : x.1 = y.1 := Subtype.ext hline
  apply Sigma.ext hflag
  rw [Subtype.heq_iff_coe_eq (by
    intro q
    rw [hline])]
  exact hpoint

/-- Every other orthogonal point gives its unique line with `p`. -/
theorem pointLineOtherToOrthogonalOther_surjective (p : Point) :
    Function.Surjective (pointLineOtherToOrthogonalOther p) := by
  intro q
  have hpq : p ≠ q.1 := Ne.symm q.2.1
  let L : Line := lineThrough p q.1 hpq q.2.2
  let flagged : PointLine p :=
    ⟨L, left_incident_lineThrough p q.1 hpq q.2.2⟩
  let other : OtherPointOn p flagged :=
    ⟨q.1, right_incident_lineThrough p q.1 hpq q.2.2, q.2.1⟩
  refine ⟨⟨flagged, other⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Flagged other points are equivalent to the 72 other orthogonal points. -/
def pointLineOtherEquiv (p : Point) :
    PointLineOtherFlag p ≃ OrthogonalOther p :=
  Equiv.ofBijective (pointLineOtherToOrthogonalOther p)
    ⟨pointLineOtherToOrthogonalOther_injective p,
      pointLineOtherToOrthogonalOther_surjective p⟩

/-- Every projective point lies on exactly nine isotropic lines. -/
theorem incident_line_card (p : Point) :
    Fintype.card (PointLine p) = 9 := by
  classical
  have hflags : Fintype.card (PointLineOtherFlag p) = 72 := by
    rw [Fintype.card_congr (pointLineOtherEquiv p), orthogonalOther_card]
  rw [Fintype.card_sigma] at hflags
  simp_rw [otherPointOn_card] at hflags
  norm_num [Finset.sum_const] at hflags
  refine Nat.mul_right_cancel (m := 8) (by norm_num) ?_
  calc
    Fintype.card (PointLine p) * 8 = 72 := hflags
    _ = 9 * 8 := by norm_num

/-- The natural incidence row sum on the point side is nine. -/
theorem incident_point_degree (p : Point) :
    ∑ L, incidenceWeight Incident p L = 9 := by
  classical
  calc
    (∑ L, incidenceWeight Incident p L) =
        (Finset.univ.filter fun L ↦ Incident p L).card := by
      simp [incidenceWeight]
    _ = Fintype.card (PointLine p) :=
      (Fintype.card_subtype _).symm
    _ = 9 := incident_line_card p

/-! ## The number of isotropic lines -/

/-- Reversing an incident point-line flag is an equivalence between the two
sigma-type enumerations. -/
def pointLineFlagSwap :
    (Σ p : Point, PointLine p) ≃
      (Σ L : Line, {p : Point // Incident p L}) where
  toFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinate line type has 585 elements. -/
theorem line_card : Fintype.card Line = 585 := by
  classical
  have hcard := Fintype.card_congr pointLineFlagSwap
  rw [Fintype.card_sigma, Fintype.card_sigma] at hcard
  simp_rw [incident_line_card, incident_point_card] at hcard
  norm_num [Finset.sum_const, point_card] at hcard
  exact Nat.mul_right_cancel (m := 9) (by norm_num) hcard.symm

/-- Model check: both sides of the incidence relation have 585 vertices and
constant degree nine. -/
theorem incidenceRegularModel :
    Fintype.card Point = 585 ∧ Fintype.card Line = 585 ∧
      (∀ p, ∑ L, incidenceWeight Incident p L = 9) ∧
      (∀ L, ∑ p, incidenceWeight Incident p L = 9) :=
  ⟨point_card, line_card, incident_point_degree, incident_line_degree⟩

end SymplecticQuadrangle
end KazhdanHyp
end GroupApproximation
