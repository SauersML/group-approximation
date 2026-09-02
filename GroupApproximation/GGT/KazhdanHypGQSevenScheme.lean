import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangleSeven
import GroupApproximation.GGT.KazhdanHypGirthEight

/-!
# The rational link scheme of the symplectic quadrangle `W(7)`

This module derives the incidence counts and strong-regularity identities for
the coordinate generalized quadrangle of order seven.  It then packages them
as `GeneralizedQuadrangleCounts`, and applies the rational two-square scheme
with the shift `mu = 15/4`.  The shift is rational even though the optimal
contraction involves the irrational number `sqrt 14`.
-/

noncomputable section

namespace GroupApproximation
namespace KazhdanHyp
namespace SymplecticQuadrangleSeven

open scoped BigOperators LinearAlgebra.Projectivization

set_option linter.unusedSimpArgs false

/-! ## The projective orthogonal hyperplane -/

/-- The hyperplane orthogonal to a projective point representative. -/
def pointOrthogonalSubmodule (p : Point) : Submodule FieldSeven Vec :=
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
    Module.finrank FieldSeven (pointOrthogonalSubmodule p) = 3 := by
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero
    (pointFunctional_ne_zero p)
  change Module.finrank FieldSeven (LinearMap.ker (form p.rep)) = 3
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
    Projectivization FieldSeven (pointOrthogonalSubmodule p) ≃
      {q : Point // form p.rep q.rep = 0} :=
  (submodulePointEquiv (pointOrthogonalSubmodule p)).trans
    (Equiv.subtypeEquivProp (by
      funext q
      apply propext
      exact mem_pointOrthogonal_projectivization_iff p q))

noncomputable instance orthogonalPointSubtypeFintype (p : Point) :
    Fintype {q : Point // form p.rep q.rep = 0} := Fintype.ofFinite _

/-- Exactly 57 projective points are orthogonal to a fixed point. -/
theorem orthogonalPoint_card (p : Point) :
    Fintype.card {q : Point // form p.rep q.rep = 0} = 57 := by
  classical
  letI : Fintype
      (Projectivization FieldSeven (pointOrthogonalSubmodule p)) :=
    Fintype.ofFinite _
  calc
    Fintype.card {q : Point // form p.rep q.rep = 0} =
        Fintype.card (Projectivization FieldSeven (pointOrthogonalSubmodule p)) :=
      Fintype.card_congr (orthogonalPointEquiv p).symm
    _ = 57 := by
      rw [← Nat.card_eq_fintype_card]
      have h := Projectivization.card_of_finrank FieldSeven
        (pointOrthogonalSubmodule p) (pointOrthogonalSubmodule_finrank p)
      rw [show Nat.card FieldSeven = 7 by
        simpa only [Nat.card_eq_fintype_card] using fieldSeven_card] at h
      norm_num at h ⊢
      exact h

/-! ## Removing the base point and counting flags -/

/-- Orthogonal projective points other than the chosen point. -/
abbrev OrthogonalOther (p : Point) :=
  {q : Point // q ≠ p ∧ form p.rep q.rep = 0}

noncomputable instance orthogonalOtherFintype (p : Point) :
    Fintype (OrthogonalOther p) := Fintype.ofFinite _

/-- Reassociate the two predicates so `Set.card_ne_eq` applies inside the
57-element orthogonal-point subtype. -/
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

/-- There are 56 orthogonal points distinct from `p`. -/
theorem orthogonalOther_card (p : Point) :
    Fintype.card (OrthogonalOther p) = 56 := by
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
    _ = 56 := by rw [orthogonalPoint_card]

/-- Isotropic lines through a fixed point. -/
abbrev PointLine (p : Point) := {L : Line // Incident p L}

noncomputable instance pointLineFintype (p : Point) : Fintype (PointLine p) :=
  Fintype.ofFinite _

/-- Points on a flagged line other than the fixed point. -/
abbrev OtherPointOn (p : Point) (L : PointLine p) :=
  {q : Point // Incident q L.1 ∧ q ≠ p}

noncomputable instance otherPointOnFintype (p : Point) (L : PointLine p) :
    Fintype (OtherPointOn p L) := Fintype.ofFinite _

/-- A flagged line through `p`, together with another point on that line. -/
abbrev PointLineOtherFlag (p : Point) :=
  Σ L : PointLine p, OtherPointOn p L

/-- Removing one specified incident point from an eight-point line leaves
seven points. -/
theorem otherPointOn_card (p : Point) (L : PointLine p) :
    Fintype.card (OtherPointOn p L) = 7 := by
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
    _ = 7 := by rw [incident_point_card]

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

/-- Flagged other points are equivalent to the 56 other orthogonal points. -/
def pointLineOtherEquiv (p : Point) :
    PointLineOtherFlag p ≃ OrthogonalOther p :=
  Equiv.ofBijective (pointLineOtherToOrthogonalOther p)
    ⟨pointLineOtherToOrthogonalOther_injective p,
      pointLineOtherToOrthogonalOther_surjective p⟩

/-- Every projective point lies on exactly eight isotropic lines. -/
theorem incident_line_card (p : Point) :
    Fintype.card (PointLine p) = 8 := by
  classical
  have hflags : Fintype.card (PointLineOtherFlag p) = 56 := by
    rw [Fintype.card_congr (pointLineOtherEquiv p), orthogonalOther_card]
  rw [Fintype.card_sigma] at hflags
  simp_rw [otherPointOn_card] at hflags
  norm_num [Finset.sum_const] at hflags
  refine Nat.mul_right_cancel (m := 7) (by norm_num) ?_
  calc
    Fintype.card (PointLine p) * 7 = 56 := hflags
    _ = 8 * 7 := by norm_num

/-- The natural incidence row sum on the point side is eight. -/
theorem incident_point_degree (p : Point) :
    ∑ L, incidenceWeight Incident p L = 8 := by
  classical
  calc
    (∑ L, incidenceWeight Incident p L) =
        (Finset.univ.filter fun L ↦ Incident p L).card := by
      simp [incidenceWeight]
    _ = Fintype.card (PointLine p) :=
      (Fintype.card_subtype _).symm
    _ = 8 := incident_line_card p

/-! ## The number of isotropic lines and two-step incidence counts -/

/-- Reversing an incident point-line flag is an equivalence between the two
sigma-type enumerations. -/
def pointLineFlagSwap :
    (Σ p : Point, PointLine p) ≃
      (Σ L : Line, {p : Point // Incident p L}) where
  toFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinate line type has 400 elements. -/
theorem line_card : Fintype.card Line = 400 := by
  classical
  have hcard := Fintype.card_congr pointLineFlagSwap
  rw [Fintype.card_sigma, Fintype.card_sigma] at hcard
  simp_rw [incident_line_card, incident_point_card] at hcard
  norm_num [Finset.sum_const, point_card] at hcard
  exact Nat.mul_right_cancel (m := 8) (by norm_num) hcard.symm

/-- Both sides of incidence have 400 vertices and constant degree eight. -/
theorem incidenceRegularModel :
    Fintype.card Point = 400 ∧ Fintype.card Line = 400 ∧
      (∀ p, ∑ L, incidenceWeight Incident p L = 8) ∧
      (∀ L, ∑ p, incidenceWeight Incident p L = 8) :=
  ⟨point_card, line_card, incident_point_degree, incident_line_degree⟩

/-- For distinct points, a common isotropic line is equivalent to
symplectic orthogonality. -/
theorem exists_incident_line_iff_orthogonal {p q : Point} (hpq : p ≠ q) :
    (∃ L, Incident p L ∧ Incident q L) ↔ form p.rep q.rep = 0 := by
  constructor
  · rintro ⟨L, hpL, hqL⟩
    exact orthogonal_of_incident hpL hqL
  · intro horth
    obtain ⟨L, hL, _⟩ := existsUnique_incident_line hpq horth
    exact ⟨L, hL⟩

/-- The number of common lines of two points is eight on the diagonal, one
for distinct orthogonal points, and zero otherwise. -/
theorem commonLine_card (p q : Point) :
    Fintype.card {L : Line // Incident p L ∧ Incident q L} =
      if p = q then 8 else if form p.rep q.rep = 0 then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    let e : {L : Line // Incident p L ∧ Incident p L} ≃
        {L : Line // Incident p L} := Equiv.subtypeEquivProp (by simp)
    exact (Fintype.card_congr e).trans
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

/-- The number of common points of two lines is eight on the diagonal, one
when concurrent, and zero otherwise. -/
theorem commonPoint_card (L M : Line) :
    Fintype.card {p : Point // Incident p L ∧ Incident p M} =
      if L = M then 8 else if ∃ p, Incident p L ∧ Incident p M then 1 else 0 := by
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

/-- The point-side two-step incidence identity. -/
theorem common_lines_count (p q : Point) :
    ∑ L, incidenceWeight Incident p L * incidenceWeight Incident q L =
      8 * (if p = q then 1 else 0) + pointCollinearityWeight Incident p q := by
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

/-- The line-side two-step incidence identity. -/
theorem common_points_count (L M : Line) :
    ∑ p, incidenceWeight Incident p L * incidenceWeight Incident p M =
      8 * (if L = M then 1 else 0) + lineConcurrencyWeight Incident L M := by
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

/-- The point-collinearity graph is 56-regular. -/
theorem point_col_degree_count (p : Point) :
    ∑ q, pointCollinearityWeight Incident q p = 56 := by
  classical
  simp_rw [pointCollinearityWeight_eq]
  calc
    (∑ q, if q ≠ p ∧ form p.rep q.rep = 0 then 1 else 0) =
        (Finset.univ.filter fun q ↦ q ≠ p ∧ form p.rep q.rep = 0).card := by
      simp
    _ = Fintype.card (OrthogonalOther p) :=
      (Fintype.card_subtype _).symm
    _ = 56 := orthogonalOther_card p

/-! ## The line-concurrency degree -/

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

/-- Removing `L` from the eight lines through a point on `L` leaves seven. -/
theorem otherLineAt_card (L : Line) (p : LinePoint L) :
    Fintype.card (OtherLineAt L p) = 7 := by
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
    _ = 7 := by rw [incident_line_card]

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

/-- The flagged other lines are equivalent to `ConcurrentOther`. -/
def linePointOtherEquiv (L : Line) :
    LinePointOtherFlag L ≃ ConcurrentOther L :=
  Equiv.ofBijective (linePointOtherToConcurrentOther L)
    ⟨linePointOtherToConcurrentOther_injective L,
      linePointOtherToConcurrentOther_surjective L⟩

/-- Every line is concurrent with exactly 56 other lines. -/
theorem concurrentOther_card (L : Line) :
    Fintype.card (ConcurrentOther L) = 56 := by
  classical
  have hflags : Fintype.card (LinePointOtherFlag L) =
      Fintype.card (ConcurrentOther L) :=
    Fintype.card_congr (linePointOtherEquiv L)
  have hpoints : Fintype.card (LinePoint L) = 8 := incident_point_card L
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

/-- The line-concurrency graph is 56-regular. -/
theorem line_col_degree_count (L : Line) :
    ∑ M, lineConcurrencyWeight Incident M L = 56 := by
  classical
  simp_rw [lineConcurrencyWeight_eq]
  calc
    (∑ M, if M ≠ L ∧ ∃ p, Incident p L ∧ Incident p M then 1 else 0) =
        (Finset.univ.filter fun M ↦
          M ≠ L ∧ ∃ p, Incident p L ∧ Incident p M).card := by
      simp
    _ = Fintype.card (ConcurrentOther L) :=
      (Fintype.card_subtype _).symm
    _ = 56 := concurrentOther_card L

/-! ## Strong regularity on the point graph -/

/-- Common collinearity neighbours of two projective points, written in
coordinate orthogonality form. -/
abbrev PointCommonNeighbor (p q : Point) :=
  {r : Point // r ≠ p ∧ form p.rep r.rep = 0 ∧
    r ≠ q ∧ form q.rep r.rep = 0}

noncomputable instance pointCommonNeighborFintype (p q : Point) :
    Fintype (PointCommonNeighbor p q) := Fintype.ofFinite _

/-- Removing two distinct specified points from an eight-point isotropic line
leaves six points. -/
theorem otherTwoPointsOnLine_card (L : Line) (p q : Point)
    (hpL : Incident p L) (hqL : Incident q L) (hpq : p ≠ q) :
    Fintype.card {r : Point // Incident r L ∧ r ≠ p ∧ r ≠ q} = 6 := by
  classical
  let S : Finset Point := Finset.univ.filter fun r ↦ Incident r L
  have hScard : S.card = 8 := by
    calc
      S.card = Fintype.card {r : Point // Incident r L} :=
        (Fintype.card_subtype _).symm
      _ = 8 := incident_point_card L
  have hpS : p ∈ S := by simp [S, hpL]
  have hqS : q ∈ S := by simp [S, hqL]
  have hqErase : q ∈ S.erase p := by simp [hqS, Ne.symm hpq]
  calc
    Fintype.card {r : Point // Incident r L ∧ r ≠ p ∧ r ≠ q} =
        (Finset.univ.filter fun r ↦
          Incident r L ∧ r ≠ p ∧ r ≠ q).card := Fintype.card_subtype _
    _ = ((S.erase p).erase q).card := by
      congr 1
      ext r
      simp [S, and_assoc, and_left_comm, and_comm]
    _ = (S.erase p).card - 1 := Finset.card_erase_of_mem hqErase
    _ = (S.card - 1) - 1 := by rw [Finset.card_erase_of_mem hpS]
    _ = 6 := by rw [hScard]

/-- If `p` and `q` are distinct and orthogonal, a point is collinear with
both exactly when it is another point of their unique line. -/
theorem pointCommonNeighbor_iff_incident_lineThrough
    {p q r : Point} (hpq : p ≠ q) (hpqOrth : form p.rep q.rep = 0) :
    (r ≠ p ∧ form p.rep r.rep = 0 ∧
        r ≠ q ∧ form q.rep r.rep = 0) ↔
      Incident r (lineThrough p q hpq hpqOrth) ∧ r ≠ p ∧ r ≠ q := by
  let L := lineThrough p q hpq hpqOrth
  have hpL : Incident p L := left_incident_lineThrough p q hpq hpqOrth
  have hqL : Incident q L := right_incident_lineThrough p q hpq hpqOrth
  constructor
  · rintro ⟨hrp, hpr, hrq, hqr⟩
    refine ⟨?_, hrp, hrq⟩
    by_contra hrL
    obtain ⟨s, hs, hunique⟩ := existsUnique_incident_orthogonal r L hrL
    have hrp' : form r.rep p.rep = 0 :=
      (form_eq_zero_comm p.rep r.rep).mp hpr
    have hrq' : form r.rep q.rep = 0 :=
      (form_eq_zero_comm q.rep r.rep).mp hqr
    have hps : p = s := hunique p ⟨hpL, hrp'⟩
    have hqs : q = s := hunique q ⟨hqL, hrq'⟩
    exact hpq (hps.trans hqs.symm)
  · rintro ⟨hrL, hrp, hrq⟩
    exact ⟨hrp, orthogonal_of_incident hpL hrL, hrq,
      orthogonal_of_incident hqL hrL⟩

/-- Adjacent points have exactly six common collinearity neighbours. -/
theorem pointCommonNeighbor_card_of_orthogonal {p q : Point}
    (hpq : p ≠ q) (hpqOrth : form p.rep q.rep = 0) :
    Fintype.card (PointCommonNeighbor p q) = 6 := by
  let L := lineThrough p q hpq hpqOrth
  let e : PointCommonNeighbor p q ≃
      {r : Point // Incident r L ∧ r ≠ p ∧ r ≠ q} :=
    Equiv.subtypeEquivProp (by
      funext r
      apply propext
      exact pointCommonNeighbor_iff_incident_lineThrough hpq hpqOrth)
  calc
    Fintype.card (PointCommonNeighbor p q) =
        Fintype.card {r : Point // Incident r L ∧ r ≠ p ∧ r ≠ q} :=
      Fintype.card_congr e
    _ = 6 := otherTwoPointsOnLine_card L p q
      (left_incident_lineThrough p q hpq hpqOrth)
      (right_incident_lineThrough p q hpq hpqOrth) hpq

/-! ## Nonadjacent common neighbours -/

/-- Projection of `q` onto a line through a nonorthogonal point `p` is a
common collinearity neighbour of `p` and `q`. -/
def lineThroughPointToCommonNeighbor (p q : Point)
    (hnon : form p.rep q.rep ≠ 0) : PointLine p → PointCommonNeighbor p q :=
  fun L ↦ by
    have hqOut : ¬ Incident q L.1 := by
      intro hqL
      exact hnon (orthogonal_of_incident L.2 hqL)
    let r := projectedPoint q L.1 hqOut
    have hrL : Incident r L.1 := projectedPoint_incident q L.1 hqOut
    have hqr : form q.rep r.rep = 0 := projectedPoint_orthogonal q L.1 hqOut
    have hrp : r ≠ p := by
      intro hrp
      apply hnon
      have hqp : form q.rep p.rep = 0 := by simpa [hrp] using hqr
      exact (form_eq_zero_comm p.rep q.rep).mpr hqp
    have hrq : r ≠ q := by
      intro hrq
      apply hqOut
      simpa [hrq] using hrL
    exact ⟨r, hrp, orthogonal_of_incident L.2 hrL, hrq, hqr⟩

/-- Distinct lines through `p` give distinct projected common neighbours. -/
theorem lineThroughPointToCommonNeighbor_injective (p q : Point)
    (hnon : form p.rep q.rep ≠ 0) :
    Function.Injective (lineThroughPointToCommonNeighbor p q hnon) := by
  intro L M hLM
  have hr : (lineThroughPointToCommonNeighbor p q hnon L).1 =
      (lineThroughPointToCommonNeighbor p q hnon M).1 :=
    congrArg (fun r : PointCommonNeighbor p q ↦ r.1) hLM
  have hpne : p ≠ (lineThroughPointToCommonNeighbor p q hnon L).1 :=
    Ne.symm (lineThroughPointToCommonNeighbor p q hnon L).2.1
  apply Subtype.ext
  apply line_unique hpne L.2
  · exact projectedPoint_incident q L.1 (by
      intro hqL
      exact hnon (orthogonal_of_incident L.2 hqL))
  · exact M.2
  · rw [hr]
    exact projectedPoint_incident q M.1 (by
      intro hqM
      exact hnon (orthogonal_of_incident M.2 hqM))

/-- Every common neighbour of nonorthogonal points is the projection onto
its unique line with `p`. -/
theorem lineThroughPointToCommonNeighbor_surjective (p q : Point)
    (hnon : form p.rep q.rep ≠ 0) :
    Function.Surjective (lineThroughPointToCommonNeighbor p q hnon) := by
  intro r
  have hpne : p ≠ r.1 := Ne.symm r.2.1
  let L : Line := lineThrough p r.1 hpne r.2.2.1
  let flagged : PointLine p :=
    ⟨L, left_incident_lineThrough p r.1 hpne r.2.2.1⟩
  have hqOut : ¬ Incident q L := by
    intro hqL
    exact hnon (orthogonal_of_incident flagged.2 hqL)
  have hrL : Incident r.1 L :=
    right_incident_lineThrough p r.1 hpne r.2.2.1
  refine ⟨flagged, ?_⟩
  apply Subtype.ext
  change projectedPoint q L hqOut = r.1
  apply Projectivization.submodule_injective
  change (Projectivization.mk'' (projectionSubmodule q L)
    (projectionSubmodule_finrank hqOut)).submodule = r.1.submodule
  rw [Projectivization.submodule_mk'']
  exact (submodule_eq_projectionSubmodule hqOut hrL r.2.2.2.2).symm

/-- Nonadjacent points have one common neighbour on each of the eight lines
through the first point. -/
theorem pointCommonNeighbor_card_of_nonorthogonal (p q : Point)
    (hnon : form p.rep q.rep ≠ 0) :
    Fintype.card (PointCommonNeighbor p q) = 8 := by
  exact (Fintype.card_congr
    (Equiv.ofBijective (lineThroughPointToCommonNeighbor p q hnon)
      ⟨lineThroughPointToCommonNeighbor_injective p q hnon,
        lineThroughPointToCommonNeighbor_surjective p q hnon⟩).symm).trans
    (incident_line_card p)

/-- The product sum of two point-collinearity columns counts their common
neighbour subtype. -/
theorem pointCollinearity_product_sum (p q : Point) :
    ∑ r, pointCollinearityWeight Incident r p *
        pointCollinearityWeight Incident r q =
      Fintype.card (PointCommonNeighbor p q) := by
  classical
  simp_rw [pointCollinearityWeight_eq]
  calc
    (∑ r,
      (if r ≠ p ∧ form p.rep r.rep = 0 then 1 else 0) *
        (if r ≠ q ∧ form q.rep r.rep = 0 then 1 else 0)) =
        ∑ r, if r ≠ p ∧ form p.rep r.rep = 0 ∧
          r ≠ q ∧ form q.rep r.rep = 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hp : r ≠ p ∧ form p.rep r.rep = 0 <;>
        by_cases hq : r ≠ q ∧ form q.rep r.rep = 0 <;> simp [hp, hq]
    _ = (Finset.univ.filter fun r ↦
        r ≠ p ∧ form p.rep r.rep = 0 ∧
          r ≠ q ∧ form q.rep r.rep = 0).card := by simp
    _ = Fintype.card (PointCommonNeighbor p q) :=
      (Fintype.card_subtype _).symm

/-- The point collinearity graph satisfies the subtraction-free strongly
regular identity used by `GeneralizedQuadrangleCounts`. -/
theorem point_col_square_count (p q : Point) :
    (∑ r, pointCollinearityWeight Incident r p *
        pointCollinearityWeight Incident r q) +
        2 * pointCollinearityWeight Incident p q +
        (if p = q then 1 else 0) =
      7 ^ 2 * (if p = q then 1 else 0) + 8 := by
  rw [pointCollinearity_product_sum]
  by_cases hpq : p = q
  · subst q
    have hcard : Fintype.card (PointCommonNeighbor p p) = 56 := by
      let e : PointCommonNeighbor p p ≃ OrthogonalOther p :=
        Equiv.subtypeEquivProp (by
          funext r
          apply propext
          constructor
          · rintro ⟨hrp, hpr, _, _⟩
            exact ⟨hrp, hpr⟩
          · rintro ⟨hrp, hpr⟩
            exact ⟨hrp, hpr, hrp, hpr⟩)
      exact (Fintype.card_congr e).trans (orthogonalOther_card p)
    rw [hcard]
    simp [pointCollinearityWeight]
  · by_cases horth : form p.rep q.rep = 0
    · rw [pointCommonNeighbor_card_of_orthogonal hpq horth]
      have hex := (exists_incident_line_iff_orthogonal hpq).mpr horth
      simp [pointCollinearityWeight, hpq, hex]
    · rw [pointCommonNeighbor_card_of_nonorthogonal p q horth]
      have hnex : ¬ ∃ L, Incident p L ∧ Incident q L :=
        fun h ↦ horth ((exists_incident_line_iff_orthogonal hpq).mp h)
      simp [pointCollinearityWeight, hpq, hnex]

/-! ## Strong regularity on the line graph -/

/-- Common concurrency neighbours of two isotropic lines. -/
abbrev LineCommonNeighbor (L M : Line) :=
  {N : Line // N ≠ L ∧ (∃ p, Incident p L ∧ Incident p N) ∧
    N ≠ M ∧ (∃ p, Incident p M ∧ Incident p N)}

noncomputable instance lineCommonNeighborFintype (L M : Line) :
    Fintype (LineCommonNeighbor L M) := Fintype.ofFinite _

/-- Removing two distinct lines from the eight lines through a point leaves
six lines. -/
theorem otherTwoLinesAtPoint_card (p : Point) (L M : Line)
    (hpL : Incident p L) (hpM : Incident p M) (hLM : L ≠ M) :
    Fintype.card {N : Line // Incident p N ∧ N ≠ L ∧ N ≠ M} = 6 := by
  classical
  let S : Finset Line := Finset.univ.filter fun N ↦ Incident p N
  have hScard : S.card = 8 := by
    calc
      S.card = Fintype.card {N : Line // Incident p N} :=
        (Fintype.card_subtype _).symm
      _ = 8 := incident_line_card p
  have hLS : L ∈ S := by simp [S, hpL]
  have hMS : M ∈ S := by simp [S, hpM]
  have hMErase : M ∈ S.erase L := by simp [hMS, Ne.symm hLM]
  calc
    Fintype.card {N : Line // Incident p N ∧ N ≠ L ∧ N ≠ M} =
        (Finset.univ.filter fun N ↦
          Incident p N ∧ N ≠ L ∧ N ≠ M).card := Fintype.card_subtype _
    _ = ((S.erase L).erase M).card := by
      congr 1
      ext N
      simp [S, and_assoc, and_left_comm, and_comm]
    _ = (S.erase L).card - 1 := Finset.card_erase_of_mem hMErase
    _ = S.card - 1 - 1 := by rw [Finset.card_erase_of_mem hLS]
    _ = 6 := by rw [hScard]

/-- For two distinct concurrent lines, every common concurrency neighbour
passes through their unique intersection point. -/
theorem lineCommonNeighbor_iff_incident_intersection
    {L M N : Line} (hLM : L ≠ M) {p : Point}
    (hpL : Incident p L) (hpM : Incident p M) :
    (N ≠ L ∧ (∃ a, Incident a L ∧ Incident a N) ∧
        N ≠ M ∧ (∃ b, Incident b M ∧ Incident b N)) ↔
      Incident p N ∧ N ≠ L ∧ N ≠ M := by
  constructor
  · rintro ⟨hNL, ⟨a, haL, haN⟩, hNM, ⟨b, hbM, hbN⟩⟩
    refine ⟨?_, hNL, hNM⟩
    by_contra hpN
    obtain ⟨s, _, hunique⟩ := existsUnique_incident_orthogonal p N hpN
    have hpa : form p.rep a.rep = 0 := orthogonal_of_incident hpL haL
    have hpb : form p.rep b.rep = 0 := orthogonal_of_incident hpM hbM
    have has : a = s := hunique a ⟨haN, hpa⟩
    have hbs : b = s := hunique b ⟨hbN, hpb⟩
    have hab : a = b := has.trans hbs.symm
    have hpaEq : p = a := by
      apply commonPoint_unique hLM hpL hpM haL
      rw [hab]
      exact hbM
    exact hpN (by simpa [hpaEq] using haN)
  · rintro ⟨hpN, hNL, hNM⟩
    exact ⟨hNL, ⟨p, hpL, hpN⟩, hNM, ⟨p, hpM, hpN⟩⟩

/-- Distinct concurrent lines have exactly six common concurrency neighbours. -/
theorem lineCommonNeighbor_card_of_concurrent {L M : Line} (hLM : L ≠ M)
    {p : Point} (hpL : Incident p L) (hpM : Incident p M) :
    Fintype.card (LineCommonNeighbor L M) = 6 := by
  let e : LineCommonNeighbor L M ≃
      {N : Line // Incident p N ∧ N ≠ L ∧ N ≠ M} :=
    Equiv.subtypeEquivProp (by
      funext N
      apply propext
      exact lineCommonNeighbor_iff_incident_intersection hLM hpL hpM)
  exact (Fintype.card_congr e).trans
    (otherTwoLinesAtPoint_card p L M hpL hpM hLM)

/-! ### Nonconcurrent lines -/

/-- A point of `L`, projected onto a nonconcurrent line `M`, determines a
line concurrent with both. -/
def pointOnLineToCommonLine (L M : Line)
    (hnon : ¬ ∃ p, Incident p L ∧ Incident p M) :
    LinePoint L → LineCommonNeighbor L M :=
  fun p ↦ by
    have hpOut : ¬ Incident p.1 M := fun hpM ↦ hnon ⟨p.1, p.2, hpM⟩
    let q := projectedPoint p.1 M hpOut
    have hqM : Incident q M := projectedPoint_incident p.1 M hpOut
    have hpqOrth : form p.1.rep q.rep = 0 :=
      projectedPoint_orthogonal p.1 M hpOut
    have hpq : p.1 ≠ q := by
      intro hpq
      exact hpOut (by simpa [hpq] using hqM)
    let N := lineThrough p.1 q hpq hpqOrth
    have hpN : Incident p.1 N :=
      left_incident_lineThrough p.1 q hpq hpqOrth
    have hqN : Incident q N :=
      right_incident_lineThrough p.1 q hpq hpqOrth
    have hNL : N ≠ L := by
      intro h
      apply hnon
      exact ⟨q, by simpa [h] using hqN, hqM⟩
    have hNM : N ≠ M := by
      intro h
      apply hpOut
      simpa [h] using hpN
    exact ⟨N, hNL, ⟨p.1, p.2, hpN⟩, hNM, ⟨q, hqM, hqN⟩⟩

/-- The common-line map sends a point of `L` to a line through that point. -/
theorem pointOnLineToCommonLine_left_incident (L M : Line)
    (hnon : ¬ ∃ p, Incident p L ∧ Incident p M) (p : LinePoint L) :
    Incident p.1 (pointOnLineToCommonLine L M hnon p) := by
  let hpOut : ¬ Incident p.1 M := fun hpM ↦ hnon ⟨p.1, p.2, hpM⟩
  let q := projectedPoint p.1 M hpOut
  have hpqOrth : form p.1.rep q.rep = 0 :=
    projectedPoint_orthogonal p.1 M hpOut
  have hpq : p.1 ≠ q := by
    intro hpq
    exact hpOut (by
      rw [hpq]
      exact projectedPoint_incident p.1 M hpOut)
  change Incident p.1 (lineThrough p.1 q hpq hpqOrth)
  exact left_incident_lineThrough p.1 q hpq hpqOrth

/-- Distinct points of `L` produce distinct common concurrent lines. -/
theorem pointOnLineToCommonLine_injective (L M : Line)
    (hnon : ¬ ∃ p, Incident p L ∧ Incident p M) :
    Function.Injective (pointOnLineToCommonLine L M hnon) := by
  intro p q hpq
  have hN : (pointOnLineToCommonLine L M hnon p).1 =
      (pointOnLineToCommonLine L M hnon q).1 :=
    congrArg (fun N : LineCommonNeighbor L M ↦ N.1) hpq
  have hother : L ≠ (pointOnLineToCommonLine L M hnon p).1 :=
    Ne.symm (pointOnLineToCommonLine L M hnon p).2.1
  apply Subtype.ext
  apply commonPoint_unique hother p.2
  · exact pointOnLineToCommonLine_left_incident L M hnon p
  · exact q.2
  · rw [hN]
    exact pointOnLineToCommonLine_left_incident L M hnon q

/-- Every common concurrency neighbour of nonconcurrent lines is obtained
from its intersection point with the first line. -/
theorem pointOnLineToCommonLine_surjective (L M : Line)
    (hnon : ¬ ∃ p, Incident p L ∧ Incident p M) :
    Function.Surjective (pointOnLineToCommonLine L M hnon) := by
  intro N
  obtain ⟨a, haL, haN⟩ := N.2.2.1
  obtain ⟨b, hbM, hbN⟩ := N.2.2.2.2
  have haOut : ¬ Incident a M := fun haM ↦ hnon ⟨a, haL, haM⟩
  have hab : a ≠ b := by
    intro hab
    apply hnon
    exact ⟨a, haL, by rw [hab]; exact hbM⟩
  have habOrth : form a.rep b.rep = 0 := orthogonal_of_incident haN hbN
  have hbProj : b = projectedPoint a M haOut := by
    apply Projectivization.submodule_injective
    change b.submodule = (Projectivization.mk'' (projectionSubmodule a M)
      (projectionSubmodule_finrank haOut)).submodule
    rw [Projectivization.submodule_mk'']
    exact submodule_eq_projectionSubmodule haOut hbM habOrth
  let flagged : LinePoint L := ⟨a, haL⟩
  refine ⟨flagged, ?_⟩
  apply Subtype.ext
  have haProj : a ≠ projectedPoint a M haOut := by
    intro h
    apply haOut
    rw [h]
    exact projectedPoint_incident a M haOut
  have haProjOrth : form a.rep (projectedPoint a M haOut).rep = 0 :=
    projectedPoint_orthogonal a M haOut
  have hProjN : Incident (projectedPoint a M haOut) N.1 := by
    rw [← hbProj]
    exact hbN
  change lineThrough a (projectedPoint a M haOut) haProj haProjOrth = N.1
  apply line_unique haProj
  · exact left_incident_lineThrough a (projectedPoint a M haOut) haProj haProjOrth
  · exact right_incident_lineThrough a (projectedPoint a M haOut) haProj haProjOrth
  · exact haN
  · exact hProjN

/-- Nonconcurrent lines have one common concurrency neighbour for each of the
eight points on the first line. -/
theorem lineCommonNeighbor_card_of_nonconcurrent (L M : Line)
    (hnon : ¬ ∃ p, Incident p L ∧ Incident p M) :
    Fintype.card (LineCommonNeighbor L M) = 8 := by
  exact (Fintype.card_congr
    (Equiv.ofBijective (pointOnLineToCommonLine L M hnon)
      ⟨pointOnLineToCommonLine_injective L M hnon,
        pointOnLineToCommonLine_surjective L M hnon⟩).symm).trans
    (incident_point_card L)

/-- The product sum of two line-concurrency columns counts their common
neighbour subtype. -/
theorem lineConcurrency_product_sum (L M : Line) :
    ∑ N, lineConcurrencyWeight Incident N L *
        lineConcurrencyWeight Incident N M =
      Fintype.card (LineCommonNeighbor L M) := by
  classical
  simp_rw [lineConcurrencyWeight_eq]
  calc
    (∑ N,
      (if N ≠ L ∧ ∃ p, Incident p L ∧ Incident p N then 1 else 0) *
        (if N ≠ M ∧ ∃ p, Incident p M ∧ Incident p N then 1 else 0)) =
        ∑ N, if N ≠ L ∧ (∃ p, Incident p L ∧ Incident p N) ∧
          N ≠ M ∧ (∃ p, Incident p M ∧ Incident p N) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro N _
      by_cases hL : N ≠ L ∧ ∃ p, Incident p L ∧ Incident p N <;>
        by_cases hM : N ≠ M ∧ ∃ p, Incident p M ∧ Incident p N <;>
          simp [hL, hM]
    _ = (Finset.univ.filter fun N ↦
        N ≠ L ∧ (∃ p, Incident p L ∧ Incident p N) ∧
          N ≠ M ∧ (∃ p, Incident p M ∧ Incident p N)).card := by
      simp
    _ = Fintype.card (LineCommonNeighbor L M) :=
      (Fintype.card_subtype _).symm

/-- The line-concurrency graph satisfies the subtraction-free strongly
regular identity used by `GeneralizedQuadrangleCounts`. -/
theorem line_col_square_count (L M : Line) :
    (∑ N, lineConcurrencyWeight Incident N L *
        lineConcurrencyWeight Incident N M) +
        2 * lineConcurrencyWeight Incident L M +
        (if L = M then 1 else 0) =
      7 ^ 2 * (if L = M then 1 else 0) + 8 := by
  rw [lineConcurrency_product_sum]
  by_cases hLM : L = M
  · subst M
    have hcard : Fintype.card (LineCommonNeighbor L L) = 56 := by
      let e : LineCommonNeighbor L L ≃ ConcurrentOther L :=
        Equiv.subtypeEquivProp (by
          funext N
          apply propext
          constructor
          · rintro ⟨hNL, hmeet, _, _⟩
            exact ⟨hNL, hmeet⟩
          · rintro ⟨hNL, hmeet⟩
            exact ⟨hNL, hmeet, hNL, hmeet⟩)
      exact (Fintype.card_congr e).trans (concurrentOther_card L)
    rw [hcard]
    simp [lineConcurrencyWeight]
  · by_cases hex : ∃ p, Incident p L ∧ Incident p M
    · obtain ⟨p, hpL, hpM⟩ := hex
      have hcon : ∃ p, Incident p L ∧ Incident p M := ⟨p, hpL, hpM⟩
      rw [lineCommonNeighbor_card_of_concurrent hLM hpL hpM]
      have hex' : ∃ p, Incident p M ∧ Incident p L := ⟨p, hpM, hpL⟩
      simp [lineConcurrencyWeight, hLM, hcon, hex']
    · rw [lineCommonNeighbor_card_of_nonconcurrent L M hex]
      have hnex' : ¬ ∃ p, Incident p M ∧ Incident p L := by
        rintro ⟨p, hpM, hpL⟩
        exact hex ⟨p, hpL, hpM⟩
      simp [lineConcurrencyWeight, hLM, hex, hnex']

/-! ## The complete W(7) association scheme -/

/-- All natural-number generalized-quadrangle counts for the algebraic
symplectic quadrangle `W(7)`. -/
def wSevenCounts : GeneralizedQuadrangleCounts Point Line where
  order := 7
  incident := Incident
  decidableIncident := incidentDecidable
  order_pos := by norm_num
  point_card := by simpa using point_card
  line_card := by simpa using line_card
  point_degree p := by simpa using incident_point_degree p
  line_degree L := by simpa using incident_line_degree L
  common_lines p q := by simpa using common_lines_count p q
  common_points L M := by simpa using common_points_count L M
  point_col_degree p := by
    have h := point_col_degree_count p
    norm_num at h ⊢
    exact h
  line_col_degree L := by
    have h := line_col_degree_count L
    norm_num at h ⊢
    exact h
  point_col_square p q := by simpa using point_col_square_count p q
  line_col_square L M := by simpa using line_col_square_count L M

/-! ## The rational shift and Gram factor -/

/-- The rational shift `15/4` satisfies the strict Zuk threshold at order
seven.  Its square is just above the optimal irrational shift `sqrt 14`. -/
theorem quadrangleMuBound_seven :
    (15 / 4 : ℚ) ^ 2 - (15 / 4 : ℚ) * (7 + 1) + 2 * 7 < 0 := by
  norm_num

/-- At order seven and shift `15/4`, the contraction is `449/960`. -/
theorem quadrangleContraction_seven :
    (2 * 7 + (15 / 4 : ℚ) ^ 2) /
        (2 * (15 / 4 : ℚ) * (7 + 1)) = 449 / 960 := by
  norm_num

/-- The rational shift gives gap `511/960`, strictly above one half. -/
theorem quadrangleGap_seven :
    (1 : ℚ) - (2 * 7 + (15 / 4 : ℚ) ^ 2) /
        (2 * (15 / 4 : ℚ) * (7 + 1)) = 511 / 960 ∧
      (1 : ℚ) / 2 < 511 / 960 := by
  constructor <;> norm_num

/-- The exact rational association scheme and square-root-free Gram factor
for the algebraic `W(7)` incidence graph. -/
def wSevenQuadrangleLinkData :
    QuadrangleLinkData wSevenCounts.Vertex := by
  apply wSevenCounts.toQuadrangleLinkData (15 / 4)
  · norm_num
  · simpa [wSevenCounts] using quadrangleMuBound_seven

/-- Model check: the symbolic certificate has degree eight and gap `511/960`. -/
theorem wSevenQuadrangleLinkData_parameters :
    wSevenQuadrangleLinkData.deg = 8 ∧
      wSevenQuadrangleLinkData.gapValue = 511 / 960 := by
  constructor <;> norm_num [wSevenQuadrangleLinkData,
    GeneralizedQuadrangleCounts.toQuadrangleLinkData,
    QuadrangleLinkData.deg, QuadrangleLinkData.gapValue,
    QuadrangleLinkData.contraction, wSevenCounts]

/-! ## The three-corner divisibility obstruction -/

/-- The total number of literal generator occurrences is three times the
number of triangles.  This is the counting identity behind the fact that a
one-vertex triangle presentation cannot have an arbitrary regular link. -/
theorem generatorOccurrenceCount_sum_three
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    ∑ i, TriangularHodgeLayer.generatorOccurrenceCount T i =
      3 * Fintype.card TriangleIndex := by
  classical
  rw [show (∑ i, TriangularHodgeLayer.generatorOccurrenceCount T i) =
      ∑ i, ∑ j, ∑ k : Fin 3, if (T j k).1 = i then 1 else 0 by
        apply Finset.sum_congr rfl
        intro i hi
        exact TriangularHodgeLayer.generatorOccurrenceCount_eq_sum T i]
  calc
    (∑ i, ∑ j, ∑ k : Fin 3, if (T j k).1 = i then 1 else 0) =
        ∑ j, ∑ i, ∑ k : Fin 3, if (T j k).1 = i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k : Fin 3, ∑ i, if (T j k).1 = i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k : Fin 3, 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      simp
    _ = 3 * Fintype.card TriangleIndex := by
      simp [Nat.mul_comm]

/-- A regular link arising from a one-vertex triangle presentation has a
multiple of three generator-degree incidences.  Equivalently, its number of
positive-to-negative directed compatible pairs is divisible by three. -/
theorem girthEightChecks_three_dvd_card_mul_degree
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (h : GirthEightChecks T d) : 3 ∣ Fintype.card Generator * d := by
  have hdegree (i : Generator) :
      TriangularHodgeLayer.generatorOccurrenceCount T i = d := by
    calc
      TriangularHodgeLayer.generatorOccurrenceCount T i =
          TriangularHodgeLayer.degree T (i, true) :=
        (TriangularHodgeLayer.degree_eq_generatorOccurrenceCount T i true).symm
      _ = d := h.regular (i, true)
  have hsum :
      (∑ i, TriangularHodgeLayer.generatorOccurrenceCount T i) =
        Fintype.card Generator * d := by
    calc
      (∑ i, TriangularHodgeLayer.generatorOccurrenceCount T i) =
          ∑ _i : Generator, d := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hdegree i
      _ = Fintype.card Generator * d := by
        simp
  refine ⟨Fintype.card TriangleIndex, ?_⟩
  calc
    Fintype.card Generator * d =
        ∑ i, TriangularHodgeLayer.generatorOccurrenceCount T i := hsum.symm
    _ = 3 * Fintype.card TriangleIndex := generatorOccurrenceCount_sum_three T

/-- The W(7) link would have `400 * 8 = 3200` directed compatible pairs. -/
theorem wSeven_directedCompatiblePairCount :
    Fintype.card (Fin 400) * 8 = 3200 := by
  norm_num

/-- The W(7) pair count is not divisible by the three cyclic corners. -/
theorem not_three_dvd_wSeven_directedCompatiblePairCount :
    ¬ 3 ∣ Fintype.card (Fin 400) * 8 := by
  norm_num

/-- No one-vertex triangle table can have the W(7) link degree and generator
count.  This is the exact divisibility obstruction, before any search. -/
theorem no_wSeven_girthEightChecks
    {TriangleIndex : Type} [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle (Fin 400))
    (h : GirthEightChecks T 8) : False := by
  exact not_three_dvd_wSeven_directedCompatiblePairCount
    (girthEightChecks_three_dvd_card_mul_degree h)

/-- The first admissible q after the q = 7 obstruction has
`585 * 9 / 3 = 1755` triangles. -/
theorem wEight_triangleCount :
    Fintype.card (Fin 585) * 9 = 3 * 1755 := by
  norm_num

/-- The next admissible example mentioned by the divisibility test is
q = 11, with `1464 * 12 / 3 = 5856` triangles. -/
theorem wEleven_triangleCount :
    Fintype.card (Fin 1464) * 12 = 3 * 5856 := by
  norm_num

/-- At q = 5 the quadratic Gram-shift inequality has no real solution, so it
has no rational solution; its discriminant is negative. -/
theorem qFive_gap_threshold_fails :
    ¬ ∃ μ : ℚ, μ ^ 2 - μ * 6 + 10 < 0 := by
  intro h
  obtain ⟨μ, hμ⟩ := h
  nlinarith [sq_nonneg (μ - 3)]

end SymplecticQuadrangleSeven
end KazhdanHyp
end GroupApproximation
