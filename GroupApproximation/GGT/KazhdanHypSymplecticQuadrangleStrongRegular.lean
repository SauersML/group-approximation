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

/-! ## Strong regularity on the line side -/

/-- Common concurrency neighbours of two isotropic lines. -/
abbrev LineCommonNeighbor (L M : Line) :=
  {N : Line // N ≠ L ∧ (∃ p, Incident p L ∧ Incident p N) ∧
    N ≠ M ∧ (∃ p, Incident p M ∧ Incident p N)}

noncomputable instance lineCommonNeighborFintype (L M : Line) :
    Fintype (LineCommonNeighbor L M) :=
  Fintype.ofFinite _

/-- Removing two distinct lines from the nine lines through a point leaves
seven lines. -/
theorem otherTwoLinesAtPoint_card (p : Point) (L M : Line)
    (hpL : Incident p L) (hpM : Incident p M) (hLM : L ≠ M) :
    Fintype.card
      {N : Line // Incident p N ∧ N ≠ L ∧ N ≠ M} = 7 := by
  classical
  let S : Finset Line := Finset.univ.filter fun N ↦ Incident p N
  have hScard : S.card = 9 := by
    calc
      S.card = Fintype.card {N : Line // Incident p N} :=
        (Fintype.card_subtype _).symm
      _ = 9 := incident_line_card p
  have hLS : L ∈ S := by simp [S, hpL]
  have hMS : M ∈ S := by simp [S, hpM]
  have hMErase : M ∈ S.erase L := by simp [hMS, Ne.symm hLM]
  calc
    Fintype.card {N : Line // Incident p N ∧ N ≠ L ∧ N ≠ M} =
        (Finset.univ.filter fun N ↦
          Incident p N ∧ N ≠ L ∧ N ≠ M).card :=
      Fintype.card_subtype _
    _ = ((S.erase L).erase M).card := by
      congr 1
      ext N
      simp [S, and_assoc, and_left_comm, and_comm]
    _ = (S.erase L).card - 1 := Finset.card_erase_of_mem hMErase
    _ = S.card - 1 - 1 := by rw [Finset.card_erase_of_mem hLS]
    _ = 7 := by rw [hScard]

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
      rw [← hab]
      exact hbM
    exact hpN (by simpa [hpaEq] using haN)
  · rintro ⟨hpN, hNL, hNM⟩
    exact ⟨hNL, ⟨p, hpL, hpN⟩, hNM, ⟨p, hpM, hpN⟩⟩

/-- Distinct concurrent lines have exactly seven common concurrency
neighbours. -/
theorem lineCommonNeighbor_card_of_concurrent {L M : Line} (hLM : L ≠ M)
    {p : Point} (hpL : Incident p L) (hpM : Incident p M) :
    Fintype.card (LineCommonNeighbor L M) = 7 := by
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
  · exact (pointOnLineToCommonLine L M hnon p).2.2.1.choose_spec.2
  · exact q.2
  · rw [hN]
    exact (pointOnLineToCommonLine L M hnon q).2.2.1.choose_spec.2

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
    exact ⟨a, haL, by simpa [hab] using hbM⟩
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
  change lineThrough a (projectedPoint a M haOut) _ _ = N.1
  apply line_unique
    (by
      intro h
      apply haOut
      rw [← h]
      exact projectedPoint_incident a M haOut)
  · exact left_incident_lineThrough a (projectedPoint a M haOut) _ _
  · rw [← hbProj]
    exact haN
  · exact right_incident_lineThrough a (projectedPoint a M haOut) _ _
  · rw [← hbProj]
    exact hbN

/-- Nonconcurrent lines have exactly nine common concurrency neighbours. -/
theorem lineCommonNeighbor_card_of_nonconcurrent (L M : Line)
    (hnon : ¬ ∃ p, Incident p L ∧ Incident p M) :
    Fintype.card (LineCommonNeighbor L M) = 9 := by
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

/-- The line concurrency graph satisfies the subtraction-free strongly
regular identity used by `GeneralizedQuadrangleCounts`. -/
theorem line_col_square_count (L M : Line) :
    (∑ N, lineConcurrencyWeight Incident N L *
        lineConcurrencyWeight Incident N M) +
        2 * lineConcurrencyWeight Incident L M +
        (if L = M then 1 else 0) =
      8 ^ 2 * (if L = M then 1 else 0) + 9 := by
  rw [lineConcurrency_product_sum]
  by_cases hLM : L = M
  · subst M
    have hcard : Fintype.card (LineCommonNeighbor L L) = 72 := by
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
      rw [lineCommonNeighbor_card_of_concurrent hLM hpL hpM]
      have hex' : ∃ p, Incident p M ∧ Incident p L := ⟨p, hpM, hpL⟩
      simp [lineConcurrencyWeight, hLM, hex, hex']
    · rw [lineCommonNeighbor_card_of_nonconcurrent L M hex]
      have hnex' : ¬ ∃ p, Incident p M ∧ Incident p L := by
        rintro ⟨p, hpM, hpL⟩
        exact hex ⟨p, hpL, hpM⟩
      simp [lineConcurrencyWeight, hLM, hex, hnex']

/-! ## The complete W(8) association scheme -/

/-- All natural-number generalized-quadrangle counts for the algebraic
symplectic quadrangle W(8).  No matrix entry or strong-regularity count is an
input to this definition. -/
def wEightCounts : GeneralizedQuadrangleCounts Point Line where
  order := 8
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

/-- The exact rational association scheme and square-root-free Gram factor
for the algebraic W(8) incidence graph. -/
def wEightQuadrangleLinkData : QuadrangleLinkData wEightCounts.Vertex :=
  wEightCounts.toQuadrangleLinkDataEight rfl

/-- Model check: the symbolic certificate has degree nine and gap `5/9`. -/
theorem wEightQuadrangleLinkData_parameters :
    wEightQuadrangleLinkData.deg = 9 ∧
      wEightQuadrangleLinkData.gapValue = 5 / 9 := by
  constructor <;> norm_num [wEightQuadrangleLinkData,
    GeneralizedQuadrangleCounts.toQuadrangleLinkDataEight,
    GeneralizedQuadrangleCounts.toQuadrangleLinkData,
    QuadrangleLinkData.deg, QuadrangleLinkData.gapValue,
    QuadrangleLinkData.contraction, wEightCounts]

end SymplecticQuadrangle
end KazhdanHyp
end GroupApproximation
