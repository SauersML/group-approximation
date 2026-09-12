import GroupApproximation.GGT.KazhdanHypTable

/-!
# The spectral bridge: a checked triangle table carries quadrangle link data

`GGT/KazhdanHypTable.lean` reduces `Hyperbolic.SharpExistence` to one table and
four statements, and calls the first of the four bookkeeping:
`QuadrangleDataOfChecks`, which says that a triangle table passing the finite
checks `TableChecks` at order `q` carries the `QuadrangleLinkData` of
`GGT/KazhdanHypQuadrangle.lean`.

This module proves it.  `quadrangleDataOfChecks` is that statement as a
theorem, so `hasKazhdanPropertyT_of_checkedTable` below is unconditional: **a
triangle table passing `TableChecks` at any order `q ≥ 7` presents a group with
Kazhdan's property `(T)`**, with no literature input, no eigenvalue estimate and
no hypothesis binder.

## What the proof is

Nine of the twelve clauses of `TableChecks` are used, and each field of
`QuadrangleLinkData` is one of them cast from `ℕ` to `ℚ`:

* `adj_symm` and `col_symm` are `adjacencyCount_comm` and its consequence for
  the derived collinearity table;
* `adj_col_sum` is the regularity clause transposed --- the link table is
  symmetric, so its column sums are the degrees;
* `adj_sign` is bipartiteness, and bipartiteness is a *consequence* of the
  positivity clause rather than a further check: a corner of a positive table
  runs from a positive letter to an inverse letter, so a nonzero adjacency
  count forces its two arguments onto opposite sides
  (`adjacencyCount_eq_zero_of_same_side`);
* `adj_square` is the simplicity clause: a count that is at most `1` is
  idempotent, so the diagonal two-step count is the degree, and off the
  diagonal the two-step count *is* `collinearityCount`, by definition;
* `col_col_sum`, `col_sign` and `col_square` are the three collinearity
  clauses, the strongly regular identity being read in the subtraction-free
  form `sum + 2 * col = q + 1` that `TableChecks` states over `ℕ`;
* `card_eq` is the generator count doubled;
* `mu_bound` is Zuk's threshold at the rational shift `mu = (q+1)/2`, where it
  reads `(q+1)² > 8q`, that is `(q-3)² > 8`, and `q ≥ 7` gives it.

The one place where the two vocabularies genuinely differ is the sign vector.
`QuadrangleLinkData` asks for a `±1`-valued function killed by the vertex sum
and diagonalising both tables; `TableChecks` never mentions one.  The bridge
supplies `tableSign`, the second coordinate of a link vertex read as a sign,
and proves its three identities from the positivity clause and from the clause
that the collinearity table vanishes across the two sides.

## What it does not do

It does not produce a table, and it touches none of the three genuinely open
residuals of the route: `CThreeTEightHyperbolicity`, `CThreeTEightInfinite` and
`TableTorsionFree` are exactly as they were, and so is `GQEightTableExists`.
`CheckedTableWitness` at the end of this module is what all four come to for a
single table.

## The checks are decidable and not evaluable as stated

`TableChecks` is a decidable predicate, and `GGT/KazhdanHypTable.lean` says a
computational lane discharges it by exhibiting bytes.  At the intended order
that is not so, by a count worth recording before anyone spends a lane on it.

At `q = 8` the link has `n = 2 * 585 = 1170` vertices and the table has
`3 * 1755 = 5265` corners, and one entry `adjacencyCount T u v` is the
cardinality of a filter over those corners, taken twice.  So

* the simplicity clause is `n² ≈ 1.4 * 10⁶` entries, each costing about
  `10⁴` corner comparisons;
* the four-cycle clause sums `n` entries for each of `n²` pairs: about
  `3 * 10⁹` entry evaluations;
* the six-cycle clause sums `n²` products for each of `n²` pairs: about
  `5 * 10¹²` entry evaluations.

No kernel evaluation reaches the third, and compiler-trusting evaluation is not an option
that this repository will take.  The clauses are stated *globally*, over all
pairs of link vertices, while the properties they express are *local*: girth at
least `8` says that the ball of radius `3` around each vertex is a tree, which
is `n * d * (d-1) * (d-1) ≈ 7 * 10⁵` steps at `d = 9`, and no four-cycle says
that the `d` neighbours of each vertex have pairwise at most one common
neighbour, which is of the same size.

So a witness has two honest routes and evaluation of the present clauses is
neither: restate the girth clauses over neighbour lists and precompute the link
as data, or --- better, since the table has to come from somewhere ---
describe the link algebraically, as the incidence graph of the symplectic
quadrangle `W(8)`, and prove the clauses from the quadrangle axioms rather than
counting.  Nothing in this module depends on which is taken: the bridge
consumes `TableChecks` and not its proof.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace KazhdanHyp

/-! ## Two elementary facts -/

private theorem bool_eq_false_of_ne_true {b : Bool} (h : b ≠ true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

private theorem bool_ne_cases {b c : Bool} (h : b ≠ c) :
    (b = true ∧ c = false) ∨ (b = false ∧ c = true) := by
  cases b
  · cases c
    · exact absurd rfl h
    · exact Or.inr ⟨rfl, rfl⟩
  · cases c
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd rfl h

private theorem nat_mul_self_of_le_one {n : ℕ} (h : n ≤ 1) : n * n = n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0]
  · rw [Nat.le_antisymm h h0]

/-! ## The bipartition sign

`TableChecks` never mentions a sign vector and `QuadrangleLinkData` asks for
one.  It is the second coordinate of a link vertex: `+1` on a positive letter,
`-1` on an inverse letter. -/

/-- The bipartition sign of a link vertex. -/
def tableSign {Generator : Type} (u : Generator × Bool) : ℚ :=
  if u.2 = true then 1 else -1

/-- The sign is valued in `±1`. -/
theorem tableSign_sq {Generator : Type} (u : Generator × Bool) :
    tableSign u * tableSign u = 1 := by
  by_cases hu : u.2 = true
  · norm_num [tableSign, hu]
  · norm_num [tableSign, bool_eq_false_of_ne_true hu]

/-- Vertices on the same side carry the same sign. -/
theorem tableSign_congr {Generator : Type} {u v : Generator × Bool}
    (h : u.2 = v.2) : tableSign u = tableSign v := by
  unfold tableSign
  rw [h]

/-- Vertices on opposite sides carry opposite signs. -/
theorem tableSign_eq_neg {Generator : Type} {u v : Generator × Bool}
    (h : u.2 ≠ v.2) : tableSign u = -tableSign v := by
  rcases bool_ne_cases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · norm_num [tableSign, hu, hv]
  · norm_num [tableSign, hu, hv]

/-- The sign product on one side is `1`. -/
theorem tableSign_mul_same {Generator : Type} {u v : Generator × Bool}
    (h : u.2 = v.2) : tableSign u * tableSign v = 1 := by
  rw [tableSign_congr h]
  exact tableSign_sq v

/-- The sign product across the two sides is `-1`. -/
theorem tableSign_mul_cross {Generator : Type} {u v : Generator × Bool}
    (h : u.2 ≠ v.2) : tableSign u * tableSign v = -1 := by
  have h1 : tableSign u * tableSign v = -(tableSign v * tableSign v) := by
    rw [tableSign_eq_neg h]
    ring
  rw [h1, tableSign_sq v]

section Table

variable {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-! ## The link of a positive table is bipartite -/

/-- **A corner of a positive table runs from a positive letter to an inverse
letter.**  Every letter of the table is positive and the target of a corner is
the *inverse* of the next letter, so a nonzero directed count puts its source
on the positive side and its target on the inverse side; in particular it
vanishes when the two vertices lie on the same side. -/
theorem directedAdjacencyCount_eq_zero_of_same_side
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hpos : ∀ j k, (T j k).2 = true) {u v : Generator × Bool} (h : u.2 = v.2) :
    TriangularHodgeLayer.directedAdjacencyCount T u v = 0 := by
  classical
  by_contra hne
  have hcard : 0 < TriangularHodgeLayer.directedAdjacencyCount T u v :=
    Nat.pos_of_ne_zero hne
  simp only [TriangularHodgeLayer.directedAdjacencyCount] at hcard
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter] at hp
  obtain ⟨-, h1, h2⟩ := hp
  have hu : u.2 = true := by
    rw [← h1]
    exact hpos p.1 p.2
  have hv : v.2 = false := by
    rw [← h2]
    show (!(T p.1 (TriangularHodgeLayer.nextCorner p.2)).2) = false
    rw [hpos]
    rfl
  rw [hu, hv] at h
  exact Bool.noConfusion h

/-- **The presentation link of a positive table is bipartite**: its two sides
are the positive letters and the inverse letters. -/
theorem adjacencyCount_eq_zero_of_same_side
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hpos : ∀ j k, (T j k).2 = true) {u v : Generator × Bool} (h : u.2 = v.2) :
    TriangularHodgeLayer.adjacencyCount T u v = 0 := by
  have hsplit : TriangularHodgeLayer.adjacencyCount T u v
      = TriangularHodgeLayer.directedAdjacencyCount T u v
        + TriangularHodgeLayer.directedAdjacencyCount T v u := rfl
  rw [hsplit, directedAdjacencyCount_eq_zero_of_same_side hpos h,
    directedAdjacencyCount_eq_zero_of_same_side hpos h.symm]

/-! ## Column sums and two-step counts -/

/-- The link table is symmetric, so a regular table has constant column sums. -/
theorem sum_adjacency_column
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {q : ℕ}
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = q + 1) (v : Generator × Bool) :
    (∑ u, TriangularHodgeLayer.adjacencyCount T u v) = q + 1 := by
  have h : (∑ u, TriangularHodgeLayer.adjacencyCount T u v)
      = TriangularHodgeLayer.degree T v := by
    simp only [TriangularHodgeLayer.degree]
    exact Finset.sum_congr rfl fun u _ =>
      TriangularHodgeLayer.adjacencyCount_comm T u v
  rw [h, hdeg v]

/-- The collinearity table vanishes on the diagonal, by definition. -/
theorem collinearityCount_self
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (v : Generator × Bool) : collinearityCount T v v = 0 := by
  unfold collinearityCount
  rw [if_pos (rfl : v = v)]

/-- The collinearity table is symmetric. -/
theorem collinearityCount_comm
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (u v : Generator × Bool) :
    collinearityCount T u v = collinearityCount T v u := by
  unfold collinearityCount
  by_cases h : u = v
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    exact Finset.sum_congr rfl fun a _ => Nat.mul_comm _ _

/-- Off the diagonal the two-step count of the link is the collinearity count,
by definition. -/
theorem sum_adjacency_offdiag
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {v v' : Generator × Bool} (h : v ≠ v') :
    (∑ u, TriangularHodgeLayer.adjacencyCount T u v
        * TriangularHodgeLayer.adjacencyCount T u v')
      = collinearityCount T v v' := by
  unfold collinearityCount
  rw [if_neg h]

/-- On the diagonal the two-step count of a simple regular link is the degree:
a count bounded by `1` is idempotent. -/
theorem sum_adjacency_diag
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {q : ℕ}
    (hsimple : ∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = q + 1) (v : Generator × Bool) :
    (∑ u, TriangularHodgeLayer.adjacencyCount T u v
        * TriangularHodgeLayer.adjacencyCount T u v) = q + 1 := by
  have hterm : ∀ u : Generator × Bool,
      TriangularHodgeLayer.adjacencyCount T u v
          * TriangularHodgeLayer.adjacencyCount T u v
        = TriangularHodgeLayer.adjacencyCount T u v :=
    fun u => nat_mul_self_of_le_one (hsimple u v)
  rw [Finset.sum_congr rfl fun u _ => hterm u]
  exact sum_adjacency_column hdeg v

/-! ## The link data of a checked table -/

/-- **The quadrangle link data of a checked table.**  Every field is one clause
of `TableChecks` cast from `ℕ` to `ℚ`, with the sign vector supplied by
`tableSign` and the rational shift taken to be `mu = (q+1)/2`, where Zuk's
threshold `mu² - mu(q+1) + 2q < 0` reads `(q+1)² > 8q` and so holds for every
`q ≥ 7`.

The hypotheses are the nine clauses of `TableChecks` that the link data needs;
`quadrangleDataOfChecks` supplies them from the checks themselves. -/
def quadrangleDataOfParts
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ)
    (hq : 7 ≤ q)
    (hpos : ∀ j k, (T j k).2 = true)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = q + 1)
    (hsimple : ∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1)
    (hcard : Fintype.card Generator = (q + 1) * (q ^ 2 + 1))
    (hcolsum : ∀ v, (∑ u, collinearityCount T u v) = q * (q + 1))
    (hcross : ∀ v v' : Generator × Bool, v.2 ≠ v'.2 → collinearityCount T v v' = 0)
    (hcolsq : ∀ v, (∑ u, collinearityCount T u v * collinearityCount T u v)
      = q * (q + 1))
    (hsr : ∀ v v' : Generator × Bool, v ≠ v' → v.2 = v'.2 →
      (∑ u, collinearityCount T u v * collinearityCount T u v')
        + 2 * collinearityCount T v v' = q + 1) :
    QuadrangleLinkData (Generator × Bool) where
  adj := fun u v => ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ)
  col := fun u v => ((collinearityCount T u v : ℕ) : ℚ)
  sign := fun u => tableSign u
  ord := (q : ℚ)
  mu := ((q : ℚ) + 1) / 2
  adj_symm := by
    intro u v
    show ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ)
        = ((TriangularHodgeLayer.adjacencyCount T v u : ℕ) : ℚ)
    rw [TriangularHodgeLayer.adjacencyCount_comm]
  col_symm := by
    intro u v
    show ((collinearityCount T u v : ℕ) : ℚ) = ((collinearityCount T v u : ℕ) : ℚ)
    rw [collinearityCount_comm]
  sign_sq := fun u => tableSign_sq u
  sign_sum := by
    show (∑ u : Generator × Bool, tableSign u) = 0
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun g _ => ?_
    calc (∑ b : Bool, tableSign ((g, b) : Generator × Bool))
        = tableSign ((g, true) : Generator × Bool)
          + tableSign ((g, false) : Generator × Bool) := by rw [Fintype.sum_bool]
      _ = 0 := by norm_num [tableSign]
  adj_col_sum := by
    intro v
    show (∑ u, ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ)) = (q : ℚ) + 1
    exact_mod_cast sum_adjacency_column hdeg v
  adj_sign := by
    intro v
    show (∑ u, ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ) * tableSign u)
        = -((q : ℚ) + 1) * tableSign v
    have hterm : ∀ u : Generator × Bool,
        ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ) * tableSign u
          = ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ) * -tableSign v := by
      intro u
      by_cases hs : u.2 = v.2
      · rw [adjacencyCount_eq_zero_of_same_side hpos hs]
        norm_num
      · rw [tableSign_eq_neg hs]
    have hsum : (∑ u, ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ))
        = (q : ℚ) + 1 := by
      exact_mod_cast sum_adjacency_column hdeg v
    rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.sum_mul, hsum]
    ring
  col_col_sum := by
    intro v
    show (∑ u, ((collinearityCount T u v : ℕ) : ℚ)) = (q : ℚ) * ((q : ℚ) + 1)
    exact_mod_cast hcolsum v
  col_sign := by
    intro v
    show (∑ u, ((collinearityCount T u v : ℕ) : ℚ) * tableSign u)
        = ((q : ℚ) * ((q : ℚ) + 1)) * tableSign v
    have hterm : ∀ u : Generator × Bool,
        ((collinearityCount T u v : ℕ) : ℚ) * tableSign u
          = ((collinearityCount T u v : ℕ) : ℚ) * tableSign v := by
      intro u
      by_cases hs : u.2 = v.2
      · rw [tableSign_congr hs]
      · rw [hcross u v hs]
        norm_num
    have hsum : (∑ u, ((collinearityCount T u v : ℕ) : ℚ))
        = (q : ℚ) * ((q : ℚ) + 1) := by
      exact_mod_cast hcolsum v
    rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.sum_mul]
    exact congrArg (fun z : ℚ => z * tableSign v) hsum
  adj_square := by
    intro v v'
    show (∑ u, ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ)
            * ((TriangularHodgeLayer.adjacencyCount T u v' : ℕ) : ℚ))
        = ((q : ℚ) + 1) * (if v = v' then 1 else 0)
          + ((collinearityCount T v v' : ℕ) : ℚ)
    have hterm : ∀ u : Generator × Bool,
        ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ)
            * ((TriangularHodgeLayer.adjacencyCount T u v' : ℕ) : ℚ)
          = ((TriangularHodgeLayer.adjacencyCount T u v
              * TriangularHodgeLayer.adjacencyCount T u v' : ℕ) : ℚ) := by
      intro u
      push_cast
      ring
    rw [Finset.sum_congr rfl fun u _ => hterm u]
    by_cases hvv : v = v'
    · subst hvv
      have hif : (if v = v then (1 : ℚ) else 0) = 1 := if_pos rfl
      have hsum : (∑ u, ((TriangularHodgeLayer.adjacencyCount T u v
            * TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ)) = (q : ℚ) + 1 := by
        exact_mod_cast sum_adjacency_diag hsimple hdeg v
      rw [hif, hsum, collinearityCount_self T v]
      push_cast
      ring
    · have hif : (if v = v' then (1 : ℚ) else 0) = 0 := if_neg hvv
      have hsum : (∑ u, ((TriangularHodgeLayer.adjacencyCount T u v
            * TriangularHodgeLayer.adjacencyCount T u v' : ℕ) : ℚ))
          = ((collinearityCount T v v' : ℕ) : ℚ) := by
        exact_mod_cast sum_adjacency_offdiag T hvv
      rw [hif, hsum]
      ring
  col_square := by
    intro v v'
    show (∑ u, ((collinearityCount T u v : ℕ) : ℚ)
            * ((collinearityCount T u v' : ℕ) : ℚ))
        = ((q : ℚ) ^ 2 - 1) * (if v = v' then 1 else 0)
          - 2 * ((collinearityCount T v v' : ℕ) : ℚ)
          + (((q : ℚ) + 1) / 2) * (1 + tableSign v * tableSign v')
    have hterm : ∀ u : Generator × Bool,
        ((collinearityCount T u v : ℕ) : ℚ) * ((collinearityCount T u v' : ℕ) : ℚ)
          = ((collinearityCount T u v * collinearityCount T u v' : ℕ) : ℚ) := by
      intro u
      push_cast
      ring
    rw [Finset.sum_congr rfl fun u _ => hterm u]
    by_cases hvv : v = v'
    · subst hvv
      have hif : (if v = v then (1 : ℚ) else 0) = 1 := if_pos rfl
      have hsum : (∑ u, ((collinearityCount T u v * collinearityCount T u v : ℕ) : ℚ))
          = (q : ℚ) * ((q : ℚ) + 1) := by
        exact_mod_cast hcolsq v
      rw [hif, hsum, collinearityCount_self T v, tableSign_sq v]
      push_cast
      ring
    · by_cases hside : v.2 = v'.2
      · have hif : (if v = v' then (1 : ℚ) else 0) = 0 := if_neg hvv
        have hsign : tableSign v * tableSign v' = 1 := tableSign_mul_same hside
        have hsum : (∑ u, ((collinearityCount T u v
              * collinearityCount T u v' : ℕ) : ℚ))
            = ((q : ℚ) + 1) - 2 * ((collinearityCount T v v' : ℕ) : ℚ) := by
          have hnat := hsr v v' hvv hside
          have hcast : ((∑ u, collinearityCount T u v
                * collinearityCount T u v' : ℕ) : ℚ)
              + 2 * ((collinearityCount T v v' : ℕ) : ℚ) = (q : ℚ) + 1 := by
            exact_mod_cast hnat
          have hsplit : ((∑ u, collinearityCount T u v
                * collinearityCount T u v' : ℕ) : ℚ)
              = ∑ u, ((collinearityCount T u v
                * collinearityCount T u v' : ℕ) : ℚ) := Nat.cast_sum _ _
          rw [hsplit] at hcast
          linarith [hcast]
        rw [hif, hsum, hsign]
        ring
      · have hif : (if v = v' then (1 : ℚ) else 0) = 0 := if_neg hvv
        have hsign : tableSign v * tableSign v' = -1 := tableSign_mul_cross hside
        have hzero : ∀ u : Generator × Bool,
            ((collinearityCount T u v * collinearityCount T u v' : ℕ) : ℚ) = 0 := by
          intro u
          by_cases hu : u.2 = v.2
          · have hu' : u.2 ≠ v'.2 := by
              rw [hu]
              exact hside
            have hz : collinearityCount T u v * collinearityCount T u v' = 0 := by
              simp [hcross u v' hu']
            exact_mod_cast hz
          · have hz : collinearityCount T u v * collinearityCount T u v' = 0 := by
              simp [hcross u v hu]
            exact_mod_cast hz
        rw [Finset.sum_eq_zero fun u _ => hzero u, hif, hsign,
          hcross v v' hside]
        push_cast
        ring
  card_eq := by
    show ((Fintype.card (Generator × Bool) : ℕ) : ℚ)
        = 2 * ((q : ℚ) + 1) * ((q : ℚ) ^ 2 + 1)
    have h : ((Fintype.card (Generator × Bool) : ℕ) : ℚ)
        = ((Fintype.card Generator : ℕ) : ℚ) * 2 := by
      rw [Fintype.card_prod, Fintype.card_bool]
      push_cast
      ring
    rw [h, hcard]
    push_cast
    ring
  ord_pos := by
    have h : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    show (0 : ℚ) < (q : ℚ)
    linarith
  mu_pos := by
    have h : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    show (0 : ℚ) < ((q : ℚ) + 1) / 2
    linarith
  mu_bound := by
    have h : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    have hp : (0 : ℚ) ≤ ((q : ℚ) - 7) * ((q : ℚ) + 1) :=
      mul_nonneg (by linarith) (by linarith)
    show (((q : ℚ) + 1) / 2) ^ 2 - (((q : ℚ) + 1) / 2) * ((q : ℚ) + 1)
        + 2 * (q : ℚ) < 0
    nlinarith [hp]

end Table

/-! ## The bridge -/

/-- **A checked table carries quadrangle link data.**  This is
`GGT/KazhdanHypTable.lean`'s `QuadrangleDataOfChecks`, proved: the nine clauses
of `TableChecks` that the link data needs are exactly its fields, cast from `ℕ`
to `ℚ`, and the sign vector the checks do not mention is `tableSign`. -/
theorem quadrangleDataOfChecks : QuadrangleDataOfChecks := by
  intro Generator TriangleIndex fg dg ng ft dt T q h
  obtain ⟨hq, hpos, hdeg, hsimple, -, -, -, hcard, hcolsum, hcross, hcolsq, hsr⟩ := h
  exact ⟨quadrangleDataOfParts T q hq hpos hdeg hsimple hcard hcolsum hcross hcolsq hsr,
    fun _ _ => rfl, rfl⟩

/-! ## What the bridge makes unconditional -/

/-- **A triangle table passing the finite checks presents a Kazhdan group.**

No hypothesis beyond the checks: `hasKazhdanPropertyT_of_tableChecks` with its
one input discharged by `quadrangleDataOfChecks`.  Every analytic and spectral
step is proved --- the two completed squares of
`GGT/KazhdanHypQuadrangle.lean`, the `k = 3` link certificate of
`GGT/KazhdanHypPolygonal.lean`, and the Garland certificate of
`Kazhdan/TriangularHodgeLayer.lean` --- so what a witness has to supply is a
finite table and nothing else. -/
theorem hasKazhdanPropertyT_of_checkedTable
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ)
    (h : TableChecks T q) :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T) :=
  hasKazhdanPropertyT_of_tableChecks quadrangleDataOfChecks T q h

/-- **`SharpExistence` from a checked table and the three residuals.**  The
spectral bridge is gone from the hypothesis list: what remains is
hyperbolicity, infiniteness and torsion-freeness of a `C(3)`-`T(8)` table
group, and one table. -/
theorem sharpExistence_of_checkedTable
    {extra : ∀ (G TI : Type), (TI → TriangularHodgeLayer.Triangle G) → Prop}
    (hhyp : CThreeTEightHyperbolicity)
    (hinf : CThreeTEightInfinite)
    (htf : TableTorsionFree extra)
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ)
    (h : TableChecks T q) (hextra : extra Generator TriangleIndex T) :
    Hyperbolic.SharpExistence :=
  sharpExistence_of_tableChecks quadrangleDataOfChecks hhyp hinf htf T q h hextra

/-! ## The whole remaining obligation, as one statement -/

/-- **What the route still owes, in one `Prop`.**  A triangle table passing the
finite checks whose group is infinite, torsion-free and hyperbolic.

This is strictly weaker than the four hypotheses of
`sharpExistence_of_tableChecks`, which quantify over *every* table passing the
checks: here the three group-theoretic clauses are asked of the one table that
is exhibited.  Property `(T)` and finite presentation do not appear, because
they are theorems --- `hasKazhdanPropertyT_of_checkedTable` and the
presentation itself.

Nothing here proves it and nothing assumes it.  Two of its four clauses are
what `C(3)`-`T(8)` small cancellation is for, the third is the
Kangaslampi--Vdovina criterion, and the table itself is a construction that the
sources consulted do not record at order `8`. -/
def CheckedTableWitness : Prop :=
  ∃ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ),
    TableChecks T q ∧
      Infinite (TriangularHodgeLayer.Presented T) ∧
      IsPowerTorsionFree (TriangularHodgeLayer.Presented T) ∧
      Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T)

/-- **`SharpExistence` from the one remaining obligation.**  Property `(T)` is
supplied by the checks alone, so this reduction consumes nothing else. -/
theorem sharpExistence_of_checkedTableWitness (h : CheckedTableWitness) :
    Hyperbolic.SharpExistence := by
  obtain ⟨Generator, TriangleIndex, fg, dg, ng, ft, dt, T, q, hchecks, hinf, htf, hhyp⟩ := h
  exact ⟨TriangularHodgeLayer.Presented T, inferInstance, hinf, inferInstance, htf,
    hhyp, hasKazhdanPropertyT_of_checkedTable T q hchecks⟩

end KazhdanHyp
end GroupApproximation
