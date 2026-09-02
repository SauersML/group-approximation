import GroupApproximation.GGT.KazhdanHypQuadrangle

/-!
# Generalized-quadrangle incidence counts imply the rational link scheme

The spectral calculation in `GGT/KazhdanHypQuadrangle.lean` consumes two
matrix identities over `ℚ`.  Checking those identities entry by entry on the
`1170` vertices of the incidence graph of `W(8)` would make the witness
unnecessarily expensive for the kernel.  This module proves the identities
once from the standard finite incidence counts of a generalized quadrangle.

`GeneralizedQuadrangleCounts P L` uses separate finite types for points and
lines.  Its fields are the subtraction-free counting form of the axioms for a
generalized quadrangle of order `(q,q)`:

* every point and line has `q+1` incidences;
* two vertices on one side have `q+1`, one, or zero common neighbours;
* the collinearity graphs are `q(q+1)`-regular;
* their common-neighbour count has strongly regular parameters
  `((q+1)(q^2+1), q(q+1), q-1, q+1)`.

The last count is written

```
  C^2 + 2 C + delta = q^2 delta + (q+1),
```

so it is an equality in `ℕ`; no truncated subtraction occurs.  The theorem
`GeneralizedQuadrangleCounts.toQuadrangleLinkData` casts these finite counts
to `ℚ` and constructs the exact data used by the rational Gram factor.  At
order eight, `mu = 4` gives gap `5/9`.

The count formulation is the interface that the coordinate construction of
the symplectic quadrangle must instantiate.  It is much smaller than either a
stored adjacency matrix or the desired property `(T)` conclusion.
-/

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

set_option linter.unusedSimpArgs false

universe u v

/-- The indicator of an incidence relation, as a natural number. -/
def incidenceWeight {Point Line : Type*} (incident : Point → Line → Prop)
    [DecidableRel incident]
    (p : Point) (l : Line) : ℕ :=
  if incident p l then 1 else 0

/-- Distinct points are collinear when they lie on a common line. -/
def pointCollinearityWeight {Point Line : Type*} [DecidableEq Point]
    [Fintype Line]
    (incident : Point → Line → Prop)
    [DecidableRel incident]
    (p p' : Point) : ℕ :=
  if p = p' then 0 else if ∃ l, incident p l ∧ incident p' l then 1 else 0

/-- Distinct lines are concurrent when they contain a common point. -/
def lineConcurrencyWeight {Point Line : Type*} [Fintype Point]
    [DecidableEq Line]
    (incident : Point → Line → Prop)
    [DecidableRel incident]
    (l l' : Line) : ℕ :=
  if l = l' then 0 else if ∃ p, incident p l ∧ incident p l' then 1 else 0

/-- Finite subtraction-free incidence counts for a generalized quadrangle of
order `(q,q)`.

For a coordinate model the first four square identities follow from the usual
unique-line and unique-projection axioms.  They are exposed as natural-number
counts here so a concrete model can prove them by structured finite-field
arguments and the spectral consumer never enumerates the full link matrix. -/
structure GeneralizedQuadrangleCounts (Point : Type u) (Line : Type v)
    [Fintype Point] [DecidableEq Point] [Fintype Line] [DecidableEq Line] where
  /-- The order `q`. -/
  order : ℕ
  /-- Incidence between points and lines. -/
  incident : Point → Line → Prop
  /-- Coordinate incidence is decidable. -/
  decidableIncident : DecidableRel incident
  /-- The order is positive. -/
  order_pos : 0 < order
  /-- The point count. -/
  point_card : Fintype.card Point = (order + 1) * (order ^ 2 + 1)
  /-- The line count. -/
  line_card : Fintype.card Line = (order + 1) * (order ^ 2 + 1)
  /-- Every point is incident with `q+1` lines. -/
  point_degree : ∀ p, ∑ l, incidenceWeight incident p l = order + 1
  /-- Every line is incident with `q+1` points. -/
  line_degree : ∀ l, ∑ p, incidenceWeight incident p l = order + 1
  /-- The two-step incidence count on the point side. -/
  common_lines : ∀ p p',
    ∑ l, incidenceWeight incident p l * incidenceWeight incident p' l =
      (order + 1) * (if p = p' then 1 else 0) +
        pointCollinearityWeight incident p p'
  /-- The two-step incidence count on the line side. -/
  common_points : ∀ l l',
    ∑ p, incidenceWeight incident p l * incidenceWeight incident p l' =
      (order + 1) * (if l = l' then 1 else 0) +
        lineConcurrencyWeight incident l l'
  /-- The point-collinearity graph has degree `q(q+1)`. -/
  point_col_degree : ∀ p,
    ∑ p', pointCollinearityWeight incident p' p = order * (order + 1)
  /-- The line-concurrency graph has degree `q(q+1)`. -/
  line_col_degree : ∀ l,
    ∑ l', lineConcurrencyWeight incident l' l = order * (order + 1)
  /-- Subtraction-free strong regularity on the point side. -/
  point_col_square : ∀ p p',
    (∑ r, pointCollinearityWeight incident r p *
        pointCollinearityWeight incident r p') +
        2 * pointCollinearityWeight incident p p' +
        (if p = p' then 1 else 0) =
      order ^ 2 * (if p = p' then 1 else 0) + (order + 1)
  /-- Subtraction-free strong regularity on the line side. -/
  line_col_square : ∀ l l',
    (∑ r, lineConcurrencyWeight incident r l *
        lineConcurrencyWeight incident r l') +
        2 * lineConcurrencyWeight incident l l' +
        (if l = l' then 1 else 0) =
      order ^ 2 * (if l = l' then 1 else 0) + (order + 1)

attribute [instance] GeneralizedQuadrangleCounts.decidableIncident

namespace GeneralizedQuadrangleCounts

variable {Point : Type u} {Line : Type v}
  [Fintype Point] [DecidableEq Point] [Fintype Line] [DecidableEq Line]
  (G : GeneralizedQuadrangleCounts Point Line)

/-- The bipartite vertex type of the incidence graph. -/
abbrev Vertex (_G : GeneralizedQuadrangleCounts Point Line) := Point ⊕ Line

/-- The rational adjacency table of the incidence graph. -/
def adj : G.Vertex → G.Vertex → ℚ
  | Sum.inl p, Sum.inr l => incidenceWeight G.incident p l
  | Sum.inr l, Sum.inl p => incidenceWeight G.incident p l
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

/-- Collinearity on points and concurrency on lines, with zero cross terms. -/
def col : G.Vertex → G.Vertex → ℚ
  | Sum.inl p, Sum.inl p' => pointCollinearityWeight G.incident p p'
  | Sum.inr l, Sum.inr l' => lineConcurrencyWeight G.incident l l'
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

/-- The sign of the bipartition. -/
def sign : G.Vertex → ℚ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

theorem pointCollinearityWeight_comm (p p' : Point) :
    pointCollinearityWeight G.incident p p' =
      pointCollinearityWeight G.incident p' p := by
  unfold pointCollinearityWeight
  by_cases h : p = p'
  · subst p'
    simp
  · rw [if_neg h, if_neg (Ne.symm h)]
    congr 1
    apply propext
    constructor
    · rintro ⟨l, hp, hp'⟩
      exact ⟨l, hp', hp⟩
    · rintro ⟨l, hp', hp⟩
      exact ⟨l, hp, hp'⟩

theorem lineConcurrencyWeight_comm (l l' : Line) :
    lineConcurrencyWeight G.incident l l' =
      lineConcurrencyWeight G.incident l' l := by
  unfold lineConcurrencyWeight
  by_cases h : l = l'
  · subst l'
    simp
  · rw [if_neg h, if_neg (Ne.symm h)]
    congr 1
    apply propext
    constructor
    · rintro ⟨p, hl, hl'⟩
      exact ⟨p, hl', hl⟩
    · rintro ⟨p, hl', hl⟩
      exact ⟨p, hl, hl'⟩

theorem adj_symm (x y : G.Vertex) : G.adj x y = G.adj y x := by
  cases x <;> cases y <;> rfl

theorem col_symm (x y : G.Vertex) : G.col x y = G.col y x := by
  cases x with
  | inl p =>
      cases y with
      | inl p' =>
          change (pointCollinearityWeight G.incident p p' : ℚ) =
            pointCollinearityWeight G.incident p' p
          exact_mod_cast G.pointCollinearityWeight_comm p p'
      | inr _ => rfl
  | inr l =>
      cases y with
      | inl _ => rfl
      | inr l' =>
          change (lineConcurrencyWeight G.incident l l' : ℚ) =
            lineConcurrencyWeight G.incident l' l
          exact_mod_cast G.lineConcurrencyWeight_comm l l'

theorem sign_sq (x : G.Vertex) : G.sign x * G.sign x = 1 := by
  cases x <;> norm_num [sign]

theorem sign_sum : ∑ x, G.sign x = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [sign, Finset.sum_const, nsmul_eq_mul]
  have hcard : Fintype.card Point = Fintype.card Line :=
    G.point_card.trans G.line_card.symm
  norm_num [hcard]

theorem adj_col_sum (x : G.Vertex) :
    ∑ y, G.adj y x = (G.order : ℚ) + 1 := by
  rw [Fintype.sum_sum_type]
  cases x with
  | inl p =>
      simp only [adj, Finset.sum_const_zero, zero_add]
      exact_mod_cast G.point_degree p
  | inr l =>
      simp only [adj, Finset.sum_const_zero, add_zero]
      exact_mod_cast G.line_degree l

theorem adj_sign (x : G.Vertex) :
    ∑ y, G.adj y x * G.sign y = -((G.order : ℚ) + 1) * G.sign x := by
  cases x with
  | inl p =>
      have h : (∑ l, (incidenceWeight G.incident p l : ℚ)) =
          (G.order : ℚ) + 1 := by
        exact_mod_cast G.point_degree p
      calc
        (∑ y, G.adj y (Sum.inl p) * G.sign y) =
            ∑ l, -(incidenceWeight G.incident p l : ℚ) := by
              rw [Fintype.sum_sum_type]
              simp [adj, sign]
        _ = -(∑ l, (incidenceWeight G.incident p l : ℚ)) := by
          rw [Finset.sum_neg_distrib]
        _ = -((G.order : ℚ) + 1) * G.sign (Sum.inl p) := by
          rw [h]
          simp [sign]
  | inr l =>
      have h : (∑ p, (incidenceWeight G.incident p l : ℚ)) =
          (G.order : ℚ) + 1 := by
        exact_mod_cast G.line_degree l
      calc
        (∑ y, G.adj y (Sum.inr l) * G.sign y) =
            ∑ p, (incidenceWeight G.incident p l : ℚ) := by
              rw [Fintype.sum_sum_type]
              simp [adj, sign]
        _ = (G.order : ℚ) + 1 := h
        _ = -((G.order : ℚ) + 1) * G.sign (Sum.inr l) := by
          simp [sign]

theorem col_col_sum (x : G.Vertex) :
    ∑ y, G.col y x = (G.order : ℚ) * ((G.order : ℚ) + 1) := by
  rw [Fintype.sum_sum_type]
  cases x with
  | inl p =>
      simp only [col, Finset.sum_const_zero, add_zero]
      exact_mod_cast G.point_col_degree p
  | inr l =>
      simp only [col, Finset.sum_const_zero, zero_add]
      exact_mod_cast G.line_col_degree l

theorem col_sign (x : G.Vertex) :
    ∑ y, G.col y x * G.sign y =
      (G.order : ℚ) * ((G.order : ℚ) + 1) * G.sign x := by
  cases x with
  | inl p =>
      have h : (∑ p', (pointCollinearityWeight G.incident p' p : ℚ)) =
          (G.order : ℚ) * ((G.order : ℚ) + 1) := by
        exact_mod_cast G.point_col_degree p
      rw [Fintype.sum_sum_type]
      simp only [col, sign, mul_one, zero_mul, Finset.sum_const_zero, add_zero]
      exact h
  | inr l =>
      have h : (∑ l', (lineConcurrencyWeight G.incident l' l : ℚ)) =
          (G.order : ℚ) * ((G.order : ℚ) + 1) := by
        exact_mod_cast G.line_col_degree l
      calc
        (∑ y, G.col y (Sum.inr l) * G.sign y) =
            ∑ l', -(lineConcurrencyWeight G.incident l' l : ℚ) := by
              rw [Fintype.sum_sum_type]
              simp [col, sign]
        _ = -(∑ l', (lineConcurrencyWeight G.incident l' l : ℚ)) := by
          rw [Finset.sum_neg_distrib]
        _ = (G.order : ℚ) * ((G.order : ℚ) + 1) *
            G.sign (Sum.inr l) := by
          rw [h]
          simp [sign]

theorem adj_square (x x' : G.Vertex) :
    ∑ y, G.adj y x * G.adj y x' =
      ((G.order : ℚ) + 1) * (if x = x' then 1 else 0) + G.col x x' := by
  rw [Fintype.sum_sum_type]
  cases x with
  | inl p =>
      cases x' with
      | inl p' =>
          simp only [adj, col, zero_mul, Finset.sum_const_zero, zero_add,
            Sum.inl.injEq]
          exact_mod_cast G.common_lines p p'
      | inr l =>
          simp [adj, col]
  | inr l =>
      cases x' with
      | inl p =>
          simp [adj, col]
      | inr l' =>
          simp only [adj, col, zero_mul, Finset.sum_const_zero, add_zero,
            Sum.inr.injEq]
          exact_mod_cast G.common_points l l'

theorem col_square (x x' : G.Vertex) :
    ∑ y, G.col y x * G.col y x' =
      ((G.order : ℚ) ^ 2 - 1) * (if x = x' then 1 else 0) - 2 * G.col x x' +
        (((G.order : ℚ) + 1) / 2) * (1 + G.sign x * G.sign x') := by
  rw [Fintype.sum_sum_type]
  cases x with
  | inl p =>
      cases x' with
      | inl p' =>
          have h := G.point_col_square p p'
          have hq :
              (∑ r, (pointCollinearityWeight G.incident r p : ℚ) *
                  pointCollinearityWeight G.incident r p') +
                  2 * pointCollinearityWeight G.incident p p' +
                  (if p = p' then 1 else 0) =
                (G.order : ℚ) ^ 2 * (if p = p' then 1 else 0) +
                  ((G.order : ℚ) + 1) := by
            exact_mod_cast h
          simp only [col, sign, mul_one, zero_mul, Finset.sum_const_zero, add_zero,
            Sum.inl.injEq]
          linear_combination hq
      | inr l =>
          simp [col, sign]
  | inr l =>
      cases x' with
      | inl p =>
          simp [col, sign]
      | inr l' =>
          have h := G.line_col_square l l'
          have hq :
              (∑ r, (lineConcurrencyWeight G.incident r l : ℚ) *
                  lineConcurrencyWeight G.incident r l') +
                  2 * lineConcurrencyWeight G.incident l l' +
                  (if l = l' then 1 else 0) =
                (G.order : ℚ) ^ 2 * (if l = l' then 1 else 0) +
                  ((G.order : ℚ) + 1) := by
            exact_mod_cast h
          simp only [col, sign, neg_mul, mul_neg, neg_neg, mul_one, zero_mul,
            Finset.sum_const_zero, zero_add, Sum.inr.injEq]
          linear_combination hq

theorem card_eq : (Fintype.card G.Vertex : ℚ) =
    2 * ((G.order : ℚ) + 1) * ((G.order : ℚ) ^ 2 + 1) := by
  rw [Fintype.card_sum, G.point_card, G.line_card]
  push_cast
  ring

/-- The natural generalized-quadrangle counts produce exactly the rational
association-scheme data used by the two-square certificate. -/
def toQuadrangleLinkData (mu : ℚ) (hmu : 0 < mu)
    (hbound : mu ^ 2 - mu * ((G.order : ℚ) + 1) + 2 * G.order < 0) :
    QuadrangleLinkData G.Vertex where
  adj := G.adj
  col := G.col
  sign := G.sign
  ord := G.order
  mu := mu
  adj_symm := G.adj_symm
  col_symm := G.col_symm
  sign_sq := G.sign_sq
  sign_sum := G.sign_sum
  adj_col_sum := G.adj_col_sum
  adj_sign := G.adj_sign
  col_col_sum := G.col_col_sum
  col_sign := G.col_sign
  adj_square := G.adj_square
  col_square := G.col_square
  card_eq := G.card_eq
  ord_pos := by exact_mod_cast G.order_pos
  mu_pos := hmu
  mu_bound := hbound

/-- At order eight the integer shift four gives the exact `5/9`-gap
certificate without an eigenvalue or a square root. -/
def toQuadrangleLinkDataEight (horder : G.order = 8) :
    QuadrangleLinkData G.Vertex := by
  apply G.toQuadrangleLinkData 4
  · norm_num
  · rw [horder]
    norm_num

/-! ## A small nondegenerate model -/

/-- The incidence graph of the thin generalized quadrangle of order one is
the eight-cycle.  This model checks that the natural-number interface is
satisfiable and that none of its degree or square clauses is vacuous. -/
def thinQuadrangle : GeneralizedQuadrangleCounts (Fin 4) (Fin 4) where
  order := 1
  incident := fun p l => p = l ∨ p = l + 1
  decidableIncident := by infer_instance
  order_pos := by norm_num
  point_card := by decide
  line_card := by decide
  point_degree := by decide
  line_degree := by decide
  common_lines := by decide
  common_points := by decide
  point_col_degree := by decide
  line_col_degree := by decide
  point_col_square := by decide
  line_col_square := by decide

/-- The thin model has eight link vertices and degree two. -/
theorem thinQuadrangle_card_degree :
    Fintype.card thinQuadrangle.Vertex = 8 ∧
      (∀ x, ∑ y, thinQuadrangle.adj y x = (2 : ℚ)) := by
  constructor
  · decide
  · intro x
    have h := thinQuadrangle.adj_col_sum x
    change (∑ y, thinQuadrangle.adj y x) =
      (thinQuadrangle.order : ℚ) + 1 at h
    norm_num [thinQuadrangle] at h
    rw [Fintype.sum_sum_type]
    exact h

end GeneralizedQuadrangleCounts
end KazhdanHyp
end GroupApproximation
