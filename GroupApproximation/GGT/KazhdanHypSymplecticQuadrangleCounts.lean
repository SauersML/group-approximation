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

noncomputable instance fieldEightDecidableEqCounts : DecidableEq FieldEight :=
  Classical.decEq FieldEight

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

/-! ## One- and two-step incidence counts -/

/-- For distinct points, having a common isotropic line is equivalent to the
symplectic orthogonality equation. -/
theorem exists_incident_line_iff_orthogonal {p q : Point} (hpq : p ≠ q) :
    (∃ L, Incident p L ∧ Incident q L) ↔ form p.rep q.rep = 0 := by
  constructor
  · rintro ⟨L, hpL, hqL⟩
    exact orthogonal_of_incident hpL hqL
  · intro horth
    obtain ⟨L, hL, _⟩ := existsUnique_incident_line hpq horth
    exact ⟨L, hL⟩

/-- The number of common lines of two points is nine on the diagonal, one
for distinct orthogonal points, and zero otherwise. -/
theorem commonLine_card (p q : Point) :
    Fintype.card {L : Line // Incident p L ∧ Incident q L} =
      if p = q then 9 else if form p.rep q.rep = 0 then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    exact (Fintype.card_congr (Equiv.subtypeEquivProp (by simp))).trans
      (incident_line_card p)
  · rw [if_neg hpq]
    by_cases horth : form p.rep q.rep = 0
    · rw [if_pos horth]
      obtain ⟨L, hL, hunique⟩ := existsUnique_incident_line hpq horth
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨L, hL⟩, ?_⟩
      intro M
      exact Subtype.ext (hunique M.1 M.2)
    · rw [if_neg horth, Fintype.card_eq_zero_iff]
      exact ⟨fun L ↦ horth
        ((exists_incident_line_iff_orthogonal hpq).mp ⟨L.1, L.2⟩)⟩

/-- Two distinct isotropic lines have at most one common point. -/
theorem commonPoint_unique {L M : Line} (hLM : L ≠ M)
    {p q : Point} (hpL : Incident p L) (hpM : Incident p M)
    (hqL : Incident q L) (hqM : Incident q M) : p = q := by
  by_contra hpq
  exact hLM (line_unique hpq hpL hqL hpM hqM)

/-- The number of common points of two lines is nine on the diagonal, one
when they are concurrent, and zero otherwise. -/
theorem commonPoint_card (L M : Line) :
    Fintype.card {p : Point // Incident p L ∧ Incident p M} =
      if L = M then 9 else if ∃ p, Incident p L ∧ Incident p M then 1 else 0 := by
  classical
  by_cases hLM : L = M
  · subst M
    rw [if_pos rfl]
    exact (Fintype.card_congr (Equiv.subtypeEquivProp (by simp))).trans
      (incident_point_card L)
  · rw [if_neg hLM]
    by_cases hex : ∃ p, Incident p L ∧ Incident p M
    · rw [if_pos hex]
      obtain ⟨p, hp⟩ := hex
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨p, hp⟩, ?_⟩
      intro q
      exact Subtype.ext
        (commonPoint_unique hLM q.2.1 q.2.2 hp.1 hp.2)
    · rw [if_neg hex, Fintype.card_eq_zero_iff]
      exact ⟨fun p ↦ hex ⟨p.1, p.2⟩⟩

/-- A sum of incidence-indicator products is the cardinality of the common
incidence subtype. -/
theorem incidence_product_sum_point (p q : Point) :
    ∑ L, incidenceWeight Incident p L * incidenceWeight Incident q L =
      Fintype.card {L : Line // Incident p L ∧ Incident q L} := by
  classical
  calc
    (∑ L, incidenceWeight Incident p L * incidenceWeight Incident q L) =
        ∑ L, if Incident p L ∧ Incident q L then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro L _
      by_cases hp : Incident p L <;> by_cases hq : Incident q L <;>
        simp [incidenceWeight, hp, hq]
    _ = (Finset.univ.filter fun L ↦ Incident p L ∧ Incident q L).card := by
      simp
    _ = Fintype.card {L : Line // Incident p L ∧ Incident q L} :=
      (Fintype.card_subtype _).symm

/-- The point-side two-step incidence identity required by
`GeneralizedQuadrangleCounts`. -/
theorem common_lines_count (p q : Point) :
    ∑ L, incidenceWeight Incident p L * incidenceWeight Incident q L =
      9 * (if p = q then 1 else 0) + pointCollinearityWeight Incident p q := by
  rw [incidence_product_sum_point, commonLine_card]
  unfold pointCollinearityWeight
  by_cases hpq : p = q
  · subst q
    simp
  · rw [if_neg hpq]
    have hiff := exists_incident_line_iff_orthogonal hpq
    by_cases horth : form p.rep q.rep = 0
    · have hex : ∃ L, Incident p L ∧ Incident q L := hiff.mpr horth
      simp [hpq, horth, hex]
    · have hnex : ¬ ∃ L, Incident p L ∧ Incident q L :=
        fun h ↦ horth (hiff.mp h)
      simp [hpq, horth, hnex]

/-- The line-side incidence-indicator product sum is the common-point
cardinality. -/
theorem incidence_product_sum_line (L M : Line) :
    ∑ p, incidenceWeight Incident p L * incidenceWeight Incident p M =
      Fintype.card {p : Point // Incident p L ∧ Incident p M} := by
  classical
  calc
    (∑ p, incidenceWeight Incident p L * incidenceWeight Incident p M) =
        ∑ p, if Incident p L ∧ Incident p M then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hL : Incident p L <;> by_cases hM : Incident p M <;>
        simp [incidenceWeight, hL, hM]
    _ = (Finset.univ.filter fun p ↦ Incident p L ∧ Incident p M).card := by
      simp
    _ = Fintype.card {p : Point // Incident p L ∧ Incident p M} :=
      (Fintype.card_subtype _).symm

/-- The line-side two-step incidence identity required by
`GeneralizedQuadrangleCounts`. -/
theorem common_points_count (L M : Line) :
    ∑ p, incidenceWeight Incident p L * incidenceWeight Incident p M =
      9 * (if L = M then 1 else 0) + lineConcurrencyWeight Incident L M := by
  rw [incidence_product_sum_line, commonPoint_card]
  unfold lineConcurrencyWeight
  by_cases hLM : L = M
  · subst M
    simp
  · by_cases hex : ∃ p, Incident p L ∧ Incident p M
    · simp [hLM, hex]
    · simp [hLM, hex]

/-! ## The two collinearity degrees -/

/-- The point-collinearity indicator is the indicator of being a distinct
orthogonal point. -/
theorem pointCollinearityWeight_eq (q p : Point) :
    pointCollinearityWeight Incident q p =
      if q ≠ p ∧ form p.rep q.rep = 0 then 1 else 0 := by
  unfold pointCollinearityWeight
  by_cases hqp : q = p
  · subst q
    simp
  · rw [if_neg hqp]
    have hpq : p ≠ q := Ne.symm hqp
    have hiff := exists_incident_line_iff_orthogonal hpq
    by_cases horth : form p.rep q.rep = 0
    · obtain ⟨L, hpL, hqL⟩ := hiff.mpr horth
      have hex : ∃ L, Incident q L ∧ Incident p L := ⟨L, hqL, hpL⟩
      simp [hqp, horth, hex]
    · have hnex : ¬ ∃ L, Incident q L ∧ Incident p L := by
        rintro ⟨L, hqL, hpL⟩
        exact horth (hiff.mp ⟨L, hpL, hqL⟩)
      simp [hqp, horth, hnex]

/-- The point-collinearity graph is 72-regular. -/
theorem point_col_degree_count (p : Point) :
    ∑ q, pointCollinearityWeight Incident q p = 72 := by
  classical
  simp_rw [pointCollinearityWeight_eq]
  calc
    (∑ q, if q ≠ p ∧ form p.rep q.rep = 0 then 1 else 0) =
        (Finset.univ.filter fun q ↦ q ≠ p ∧ form p.rep q.rep = 0).card := by
      simp
    _ = Fintype.card (OrthogonalOther p) :=
      (Fintype.card_subtype _).symm
    _ = 72 := orthogonalOther_card p

/-- Points on a fixed line. -/
abbrev LinePoint (L : Line) := {p : Point // Incident p L}

/-- Other lines through a flagged point of `L`. -/
abbrev OtherLineAt (L : Line) (p : LinePoint L) :=
  {M : Line // Incident p.1 M ∧ M ≠ L}

/-- A point of `L`, together with another line through that point. -/
abbrev LinePointOtherFlag (L : Line) :=
  Σ p : LinePoint L, OtherLineAt L p

/-- Lines other than `L` which are concurrent with `L`. -/
abbrev ConcurrentOther (L : Line) :=
  {M : Line // M ≠ L ∧ ∃ p, Incident p L ∧ Incident p M}

/-- Removing `L` from the nine lines through a point on `L` leaves eight. -/
theorem otherLineAt_card (L : Line) (p : LinePoint L) :
    Fintype.card (OtherLineAt L p) = 8 := by
  classical
  let e : OtherLineAt L p ≃
      {M : {N : Line // Incident p.1 N} // M ≠ ⟨L, p.2⟩} :=
    { toFun := fun M ↦ ⟨⟨M.1, M.2.1⟩, by
        intro h
        apply M.2.2
        exact congrArg (fun z : {N : Line // Incident p.1 N} ↦ z.1) h⟩
      invFun := fun M ↦ ⟨M.1.1, M.1.2, by
        intro h
        apply M.2
        exact Subtype.ext h⟩
      left_inv := by intro M; exact Subtype.ext rfl
      right_inv := by intro M; exact Subtype.ext rfl }
  calc
    Fintype.card (OtherLineAt L p) =
        Fintype.card {M : {N : Line // Incident p.1 N} // M ≠ ⟨L, p.2⟩} :=
      Fintype.card_congr e
    _ = Fintype.card {N : Line // Incident p.1 N} - 1 :=
      Set.card_ne_eq (⟨L, p.2⟩ : {N : Line // Incident p.1 N})
    _ = 8 := by rw [incident_line_card]

/-- A flagged point and another line through it determine a concurrent line. -/
def linePointOtherToConcurrentOther (L : Line) :
    LinePointOtherFlag L → ConcurrentOther L :=
  fun x ↦ ⟨x.2.1, x.2.2.2, ⟨x.1.1, x.1.2, x.2.2.1⟩⟩

/-- The flag-to-concurrent-line map is injective because distinct lines have
at most one common point. -/
theorem linePointOtherToConcurrentOther_injective (L : Line) :
    Function.Injective (linePointOtherToConcurrentOther L) := by
  intro x y hxy
  have hline : x.2.1 = y.2.1 :=
    congrArg (fun M : ConcurrentOther L ↦ M.1) hxy
  have hother : L ≠ x.2.1 := Ne.symm x.2.2.2
  have hpoint : x.1.1 = y.1.1 := by
    apply commonPoint_unique hother x.1.2 x.2.2.1 y.1.2
    rw [hline]
    exact y.2.2.1
  have hflag : x.1 = y.1 := Subtype.ext hpoint
  apply Sigma.ext hflag
  rw [Subtype.heq_iff_coe_eq (by
    intro M
    rw [hpoint])]
  exact hline

/-- Every concurrent line has its unique intersection point with `L`. -/
theorem linePointOtherToConcurrentOther_surjective (L : Line) :
    Function.Surjective (linePointOtherToConcurrentOther L) := by
  intro M
  obtain ⟨p, hpL, hpM⟩ := M.2.2
  let flagged : LinePoint L := ⟨p, hpL⟩
  let other : OtherLineAt L flagged := ⟨M.1, hpM, M.2.1⟩
  refine ⟨⟨flagged, other⟩, ?_⟩
  exact Subtype.ext rfl

/-- The 72 flagged other lines are exactly the lines concurrent with `L`. -/
def linePointOtherEquiv (L : Line) :
    LinePointOtherFlag L ≃ ConcurrentOther L :=
  Equiv.ofBijective (linePointOtherToConcurrentOther L)
    ⟨linePointOtherToConcurrentOther_injective L,
      linePointOtherToConcurrentOther_surjective L⟩

/-- Every line is concurrent with exactly 72 other lines. -/
theorem concurrentOther_card (L : Line) :
    Fintype.card (ConcurrentOther L) = 72 := by
  classical
  have hflags : Fintype.card (LinePointOtherFlag L) =
      Fintype.card (ConcurrentOther L) :=
    Fintype.card_congr (linePointOtherEquiv L)
  have hpoints : Fintype.card (LinePoint L) = 9 := incident_point_card L
  rw [Fintype.card_sigma] at hflags
  simp_rw [otherLineAt_card] at hflags
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hflags
  rw [hpoints] at hflags
  norm_num at hflags
  exact hflags.symm

/-- The line-concurrency indicator is the indicator of membership in
`ConcurrentOther`. -/
theorem lineConcurrencyWeight_eq (M L : Line) :
    lineConcurrencyWeight Incident M L =
      if M ≠ L ∧ ∃ p, Incident p L ∧ Incident p M then 1 else 0 := by
  unfold lineConcurrencyWeight
  by_cases hML : M = L
  · subst M
    simp
  · by_cases hex : ∃ p, Incident p L ∧ Incident p M
    · have hex' : ∃ p, Incident p M ∧ Incident p L := by
        obtain ⟨p, hpL, hpM⟩ := hex
        exact ⟨p, hpM, hpL⟩
      simp [hML, hex, hex']
    · have hnex' : ¬ ∃ p, Incident p M ∧ Incident p L := by
        rintro ⟨p, hpM, hpL⟩
        exact hex ⟨p, hpL, hpM⟩
      simp [hML, hex, hnex']

/-- The line-concurrency graph is 72-regular. -/
theorem line_col_degree_count (L : Line) :
    ∑ M, lineConcurrencyWeight Incident M L = 72 := by
  classical
  simp_rw [lineConcurrencyWeight_eq]
  calc
    (∑ M, if M ≠ L ∧ ∃ p, Incident p L ∧ Incident p M then 1 else 0) =
        (Finset.univ.filter fun M ↦
          M ≠ L ∧ ∃ p, Incident p L ∧ Incident p M).card := by
      simp
    _ = Fintype.card (ConcurrentOther L) :=
      (Fintype.card_subtype _).symm
    _ = 72 := concurrentOther_card L

end SymplecticQuadrangle
end KazhdanHyp
end GroupApproximation
