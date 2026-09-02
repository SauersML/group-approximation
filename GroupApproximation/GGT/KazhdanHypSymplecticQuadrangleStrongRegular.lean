import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangleCounts

/-!
# Strong regularity on the point graph of W(8)

This module counts common collinearity neighbours in the coordinate
symplectic quadrangle.  Adjacent points have the seven other points of their
unique isotropic line as common neighbours.  Nonadjacent points have one
common neighbour on each of the nine lines through the first point, supplied
by the generalized-quadrangle projection axiom.  Thus the point graph has
strongly regular parameters `(585,72,7,9)`.

These are the point-side parameters of `GQ(8,8)` in Payne--Thas,
*Finite Generalized Quadrangles*, Section 3.2.1.
-/

noncomputable section

namespace GroupApproximation
namespace KazhdanHyp
namespace SymplecticQuadrangle

open scoped BigOperators

set_option linter.unusedSimpArgs false

/-- Common collinearity neighbours of two projective points, written in
coordinate orthogonality form. -/
abbrev PointCommonNeighbor (p q : Point) :=
  {r : Point // r ≠ p ∧ form p.rep r.rep = 0 ∧
    r ≠ q ∧ form q.rep r.rep = 0}

noncomputable instance pointCommonNeighborFintype (p q : Point) :
    Fintype (PointCommonNeighbor p q) :=
  Fintype.ofFinite _

/-- Removing two distinct specified points from a nine-point isotropic line
leaves seven points. -/
theorem otherTwoPointsOnLine_card (L : Line) (p q : Point)
    (hpL : Incident p L) (hqL : Incident q L) (hpq : p ≠ q) :
    Fintype.card
      {r : Point // Incident r L ∧ r ≠ p ∧ r ≠ q} = 7 := by
  classical
  let S : Finset Point := Finset.univ.filter fun r ↦ Incident r L
  have hScard : S.card = 9 := by
    calc
      S.card = Fintype.card {r : Point // Incident r L} :=
        (Fintype.card_subtype _).symm
      _ = 9 := incident_point_card L
  have hpS : p ∈ S := by simp [S, hpL]
  have hqS : q ∈ S := by simp [S, hqL]
  have hqErase : q ∈ S.erase p := by
    simp [hqS, Ne.symm hpq]
  calc
    Fintype.card {r : Point // Incident r L ∧ r ≠ p ∧ r ≠ q} =
        (Finset.univ.filter fun r ↦
          Incident r L ∧ r ≠ p ∧ r ≠ q).card :=
      Fintype.card_subtype _
    _ = ((S.erase p).erase q).card := by
      congr 1
      ext r
      simp [S, and_assoc, and_left_comm, and_comm]
    _ = (S.erase p).card - 1 := Finset.card_erase_of_mem hqErase
    _ = (S.card - 1) - 1 := by rw [Finset.card_erase_of_mem hpS]
    _ = 7 := by rw [hScard]

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

/-- Adjacent points have exactly seven common collinearity neighbours. -/
theorem pointCommonNeighbor_card_of_orthogonal {p q : Point}
    (hpq : p ≠ q) (hpqOrth : form p.rep q.rep = 0) :
    Fintype.card (PointCommonNeighbor p q) = 7 := by
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
    _ = 7 := otherTwoPointsOnLine_card L p q
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

/-- Nonadjacent points have one common neighbour on each of the nine lines
through the first point. -/
theorem pointCommonNeighbor_card_of_nonorthogonal (p q : Point)
    (hnon : form p.rep q.rep ≠ 0) :
    Fintype.card (PointCommonNeighbor p q) = 9 := by
  exact (Fintype.card_congr
    (Equiv.ofBijective (lineThroughPointToCommonNeighbor p q hnon)
      ⟨lineThroughPointToCommonNeighbor_injective p q hnon,
        lineThroughPointToCommonNeighbor_surjective p q hnon⟩).symm).trans
    (incident_line_card p)

/-! ## The point-side strong-regularity identity -/

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
      8 ^ 2 * (if p = q then 1 else 0) + 9 := by
  rw [pointCollinearity_product_sum]
  by_cases hpq : p = q
  · subst q
    have hcard : Fintype.card (PointCommonNeighbor p p) = 72 := by
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

end SymplecticQuadrangle
end KazhdanHyp
end GroupApproximation
