import GroupApproximation.GGT.KazhdanHypGQEightTablePerPoint

/-!
# Soundness of the finite table checker: girth and the `W(8)` link

`KazhdanHypGQEightTableFormat` supplies the Boolean verifier `checkTable` and
its girth half `checkTable_true_girth`.  Its link half was stated there as
`checkW8Table_true_link`, which consumes a second Boolean `wEightLinkCheck`:
a `decide` over all `1170 * 1170` signed link pairs of a *noncomputable*
adjacency table.  That extra premise can never be discharged by the kernel, so
the endpoint would have been conditional on an unusable hypothesis.

This module removes it.  The identification of the presentation link with the
algebraic `W(8)` incidence graph is *proved* from the local checks that
`checkTable` already performs, with no enumeration and no second Boolean:

* `adjacencyCount_of_checkTable` --- the presentation-link multiplicity between
  the signed vertices `(x, true)` and `(y, false)` is exactly the indicator of
  `member T x y`, that is of `y ∈ lambda(x)`.  This is where the exact-cover
  clause `pairCoverCheck`, the cyclic-row clause `rowCompatibilityCheck`, and
  the simplicity clause of `GirthEightChecks` are consumed.  The three cyclic
  corners of a row are the only sources of link edges, and every table letter
  is positive, so the link is bipartite for the sign and the two remaining sign
  patterns contribute nothing.
* `linkIdentification_of_checkTable` --- the resulting
  `TriangleLinkIdentification` against
  `SymplecticQuadrangle.wEightQuadrangleLinkData`, along the signed-vertex map
  `wEightVertexEquiv` (a positive generator names its assigned line, a negative
  one names its point).  The `Fin 585` coordinates are connected to the
  algebraic points and lines by the `W8Table` fields `pointEquiv`, `lineEquiv`
  and `incident_spec`, which is the only place the coordinate encoding is used.

**What remains.**  Nothing: `linkIdentification_of_checkTable` and
`girthEightChecks_of_checkTable` both take exactly `checkTable T.toTable = true`
and no other hypothesis.  In particular the bijectivity of `lambda` is not an
extra input either; it is the `lambdaCheck` clause of `localCheck` and is
extracted here by `lambda_bijective_of_checkTable`.  What a *witness* still owes
is a `W8Table 1755` whose `incident_spec` holds by construction (use
`W8Table.ofCoordinate`) and for which `checkTable` evaluates to `true`;
`KazhdanHypGQEightTablePerPoint.checkTable_true_of_checkPoints` splits that
evaluation into one small kernel decision per point.
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace GroupApproximation
namespace KazhdanHyp
namespace GQEightTableFormat

open scoped BigOperators

/-! ## Corner bookkeeping for a positive table -/

/-- The three cyclic corner positions, as an explicit disjunction. -/
theorem cornerIndex_cases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Every letter of a table triangle is a positive generator. -/
theorem triangles_snd {n m : ℕ} (T : Table n m) (j : Fin m) (k : Fin 3) :
    (triangles T j k).2 = true := by
  rcases cornerIndex_cases k with rfl | rfl | rfl
  · rfl
  · rfl
  · rfl

/-- No corner of a table triangle is a negative generator. -/
theorem triangles_ne_of_false {n m : ℕ} (T : Table n m) (j : Fin m) (k : Fin 3)
    (x : Fin n) : triangles T j k ≠ (x, false) := by
  intro hcontra
  have h : (triangles T j k).2 = false := congrArg Prod.snd hcontra
  rw [triangles_snd T j k] at h
  exact Bool.noConfusion h

/-- A directed corner never starts at a negative signed generator. -/
theorem directedAdjacencyCount_of_false_source {n m : ℕ} (T : Table n m)
    (x : Fin n) (v : Fin n × Bool) :
    TriangularHodgeLayer.directedAdjacencyCount (triangles T) (x, false) v = 0 := by
  unfold TriangularHodgeLayer.directedAdjacencyCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨j, k⟩ -
  rintro ⟨h1, -⟩
  exact triangles_ne_of_false T j k x h1

/-- A directed corner never ends at a positive signed generator, because the
successor letter is inverted. -/
theorem directedAdjacencyCount_of_true_target {n m : ℕ} (T : Table n m)
    (u : Fin n × Bool) (y : Fin n) :
    TriangularHodgeLayer.directedAdjacencyCount (triangles T) u (y, true) = 0 := by
  unfold TriangularHodgeLayer.directedAdjacencyCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨j, k⟩ -
  rintro ⟨-, h2⟩
  have h : (!(triangles T j (TriangularHodgeLayer.nextCorner k)).2) = true :=
    congrArg Prod.snd h2
  rw [triangles_snd T j (TriangularHodgeLayer.nextCorner k), Bool.not_true] at h
  exact Bool.noConfusion h

/-- The presentation link of a positive table has no edge between two positive
signed generators. -/
theorem adjacencyCount_true_true {n m : ℕ} (T : Table n m) (x y : Fin n) :
    TriangularHodgeLayer.adjacencyCount (triangles T) (x, true) (y, true) = 0 := by
  have h1 : TriangularHodgeLayer.directedAdjacencyCount (triangles T)
      (x, true) (y, true) = 0 :=
    directedAdjacencyCount_of_true_target T (x, true) y
  have h2 : TriangularHodgeLayer.directedAdjacencyCount (triangles T)
      (y, true) (x, true) = 0 :=
    directedAdjacencyCount_of_true_target T (y, true) x
  unfold TriangularHodgeLayer.adjacencyCount
  omega

/-- The presentation link of a positive table has no edge between two negative
signed generators. -/
theorem adjacencyCount_false_false {n m : ℕ} (T : Table n m) (x y : Fin n) :
    TriangularHodgeLayer.adjacencyCount (triangles T) (x, false) (y, false) = 0 := by
  have h1 : TriangularHodgeLayer.directedAdjacencyCount (triangles T)
      (x, false) (y, false) = 0 :=
    directedAdjacencyCount_of_false_source T x (y, false)
  have h2 : TriangularHodgeLayer.directedAdjacencyCount (triangles T)
      (y, false) (x, false) = 0 :=
    directedAdjacencyCount_of_false_source T y (x, false)
  unfold TriangularHodgeLayer.adjacencyCount
  omega

/-- The rational form of `adjacencyCount_true_true`, so that the endpoint
computation never has to reconcile a natural-number cast with a rational
literal mid-rewrite. -/
theorem adjacencyCount_cast_true_true {n m : ℕ} (T : Table n m) (x y : Fin n) :
    (TriangularHodgeLayer.adjacencyCount (triangles T) (x, true) (y, true) : ℚ)
      = 0 := by
  norm_num [adjacencyCount_true_true]

/-- The rational form of `adjacencyCount_false_false`. -/
theorem adjacencyCount_cast_false_false {n m : ℕ} (T : Table n m) (x y : Fin n) :
    (TriangularHodgeLayer.adjacencyCount (triangles T) (x, false) (y, false) : ℚ)
      = 0 := by
  norm_num [adjacencyCount_false_false]

/-! ## Cyclic corners and the directed pairs of a row -/

/-- A cyclic corner of a row realizes one of the three directed pairs the
verifier records. -/
theorem rowContainsPair_of_corner {n m : ℕ} (T : Table n m) (j : Fin m)
    (k : Fin 3) (x y : Fin n)
    (h1 : triangles T j k = (x, true))
    (h2 : TriangularHodgeLayer.inverseSigned
      (triangles T j (TriangularHodgeLayer.nextCorner k)) = (y, false)) :
    rowContainsPair (T.rows j) x y = true := by
  have hdisj : ((T.rows j).x = x ∧ (T.rows j).y = y) ∨
      ((T.rows j).y = x ∧ (T.rows j).z = y) ∨
      ((T.rows j).z = x ∧ (T.rows j).x = y) := by
    rcases cornerIndex_cases k with rfl | rfl | rfl
    · exact Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.fst h2⟩
    · exact Or.inr (Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.fst h2⟩)
    · exact Or.inr (Or.inr ⟨congrArg Prod.fst h1, congrArg Prod.fst h2⟩)
  unfold rowContainsPair
  exact decide_eq_true hdisj

/-- Conversely, a recorded directed pair of a row is realized by a cyclic
corner. -/
theorem corner_of_rowContainsPair {n m : ℕ} (T : Table n m) (j : Fin m)
    (x y : Fin n) (h : rowContainsPair (T.rows j) x y = true) :
    ∃ k : Fin 3, triangles T j k = (x, true) ∧
      TriangularHodgeLayer.inverseSigned
        (triangles T j (TriangularHodgeLayer.nextCorner k)) = (y, false) := by
  unfold rowContainsPair at h
  have hdisj : ((T.rows j).x = x ∧ (T.rows j).y = y) ∨
      ((T.rows j).y = x ∧ (T.rows j).z = y) ∨
      ((T.rows j).z = x ∧ (T.rows j).x = y) := of_decide_eq_true h
  rcases hdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩

/-- A directed pair covered exactly once is covered by some row. -/
theorem exists_row_of_pairCoverCount {n m : ℕ} (T : Table n m) (x y : Fin n)
    (h : pairCoverCount T x y = 1) :
    ∃ j, rowContainsPair (T.rows j) x y = true := by
  by_contra hcon
  have hzero : pairCoverCount T x y = 0 := by
    unfold pairCoverCount
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun hj => hcon ⟨j, hj⟩)]
  rw [hzero] at h
  omega

/-! ## The local checks compute the link -/

/-- The three semantic facts carried by `localCheck`. -/
theorem localCheck_facts {n m : ℕ} (T : Table n m) (h : localCheck T = true) :
    Function.Bijective T.lambda ∧
      (∀ j, rowCompatible T (T.rows j) = true) ∧
      (∀ x y, pairCoverCount T x y = if member T x y = true then 1 else 0) := by
  unfold localCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_⟩
  · have hl := h.1.1.1.2
    unfold lambdaCheck at hl
    exact of_decide_eq_true hl
  · have hr := h.1.1.2
    unfold rowCompatibilityCheck at hr
    exact (allFinN_eq_true_iff _ _).mp hr
  · intro x y
    have hc := h.1.2
    unfold pairCoverCheck at hc
    have hc1 := (allFinN_eq_true_iff _ _).mp hc x
    have hc2 := (allFinN_eq_true_iff _ _).mp hc1 y
    exact of_decide_eq_true hc2

/-- **The link multiplicity of a checked table.**  For a positive table whose
rows are cyclically compatible, whose compatible directed pairs are covered
exactly once, and whose link is simple, the presentation-link edge from the
positive generator `x` to the negative generator `y` has multiplicity `1` when
`y` lies on the line `lambda x` and `0` otherwise. -/
theorem adjacencyCount_true_false {n m : ℕ} (T : Table n m)
    (hrows : ∀ j, rowCompatible T (T.rows j) = true)
    (hcover : ∀ x y : Fin n,
      pairCoverCount T x y = if member T x y = true then 1 else 0)
    (hsimple : ∀ u v, TriangularHodgeLayer.adjacencyCount (triangles T) u v ≤ 1)
    (x y : Fin n) :
    TriangularHodgeLayer.adjacencyCount (triangles T) (x, true) (y, false)
      = if member T x y = true then 1 else 0 := by
  have hzero : TriangularHodgeLayer.directedAdjacencyCount (triangles T)
      (y, false) (x, true) = 0 :=
    directedAdjacencyCount_of_false_source T y (x, true)
  have hsplit : TriangularHodgeLayer.adjacencyCount (triangles T)
      (x, true) (y, false)
      = TriangularHodgeLayer.directedAdjacencyCount (triangles T)
        (x, true) (y, false) := by
    unfold TriangularHodgeLayer.adjacencyCount
    omega
  by_cases hm : member T x y = true
  · rw [if_pos hm, hsplit]
    have hs := hsimple (x, true) (y, false)
    have hle : TriangularHodgeLayer.directedAdjacencyCount (triangles T)
        (x, true) (y, false) ≤ 1 := by omega
    have hcount : pairCoverCount T x y = 1 := by
      rw [hcover x y, if_pos hm]
    obtain ⟨j, hj⟩ := exists_row_of_pairCoverCount T x y hcount
    obtain ⟨k, h1, h2⟩ := corner_of_rowContainsPair T j x y hj
    have hpos : 0 < TriangularHodgeLayer.directedAdjacencyCount (triangles T)
        (x, true) (y, false) := by
      unfold TriangularHodgeLayer.directedAdjacencyCount
      apply Finset.card_pos.mpr
      exact ⟨(j, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
    omega
  · rw [if_neg hm, hsplit]
    unfold TriangularHodgeLayer.directedAdjacencyCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨j, k⟩ -
    rintro ⟨g1, g2⟩
    exact hm (rowContainsPair_member_of_compat T (T.rows j) x y (hrows j)
      (rowContainsPair_of_corner T j k x y g1 g2))

/-! ## The two soundness theorems consumed by the endpoint -/

/-- The girth half of the verifier, under the name used by the assembly. -/
theorem girthEightChecks_of_checkTable {n m : ℕ} (T : Table n m)
    (h : checkTable T = true) : GirthEightChecks (triangles T) 9 :=
  checkTable_true_girth T h

/-- The point-to-line map of a checked table is a bijection.  This is the
`lambdaCheck` clause; it is not an extra hypothesis of the endpoint. -/
theorem lambda_bijective_of_checkTable {n m : ℕ} (T : Table n m)
    (h : checkTable T = true) : Function.Bijective T.lambda := by
  have h9 : checkTableAt T 9 = true := h
  have hloc : localCheck T = true := checkTableAt_true_local T h9
  exact (localCheck_facts T hloc).1

/-- The link multiplicities of a checked table, in the `member` form. -/
theorem adjacencyCount_of_checkTable {n m : ℕ} (T : Table n m)
    (h : checkTable T = true) (x y : Fin n) :
    TriangularHodgeLayer.adjacencyCount (triangles T) (x, true) (y, false)
      = if member T x y = true then 1 else 0 := by
  have h9 : checkTableAt T 9 = true := h
  have hloc : localCheck T = true := checkTableAt_true_local T h9
  have hfacts := localCheck_facts T hloc
  have hgirth : GirthEightChecks (triangles T) 9 := checkTable_true_girth T h
  exact adjacencyCount_true_false T hfacts.2.1 hfacts.2.2 hgirth.simple x y

/-! ## The `W(8)` coordinate bridge -/

/-- A positive signed generator names the line assigned to it. -/
theorem wEightVertexEquiv_true {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda) (u : Fin 585) :
    wEightVertexEquiv T h (u, true) =
      Sum.inr (T.lineEquiv (T.toTable.lambda u)) := rfl

/-- A negative signed generator names its point. -/
theorem wEightVertexEquiv_false {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda) (u : Fin 585) :
    wEightVertexEquiv T h (u, false) = Sum.inl (T.pointEquiv u) := rfl

theorem wEight_adj_inl_inl (p q : SymplecticQuadrangle.Point) :
    SymplecticQuadrangle.wEightQuadrangleLinkData.adj
      (Sum.inl p) (Sum.inl q) = 0 := rfl

theorem wEight_adj_inr_inr (l l' : SymplecticQuadrangle.Line) :
    SymplecticQuadrangle.wEightQuadrangleLinkData.adj
      (Sum.inr l) (Sum.inr l') = 0 := rfl

theorem wEight_adj_inr_inl (l : SymplecticQuadrangle.Line)
    (p : SymplecticQuadrangle.Point) :
    SymplecticQuadrangle.wEightQuadrangleLinkData.adj (Sum.inr l) (Sum.inl p) =
      (incidenceWeight SymplecticQuadrangle.wEightCounts.incident p l : ℚ) := rfl

theorem wEight_adj_inl_inr (p : SymplecticQuadrangle.Point)
    (l : SymplecticQuadrangle.Line) :
    SymplecticQuadrangle.wEightQuadrangleLinkData.adj (Sum.inl p) (Sum.inr l) =
      (incidenceWeight SymplecticQuadrangle.wEightCounts.incident p l : ℚ) := rfl

theorem incidenceWeight_wEight_eq_one {p : SymplecticQuadrangle.Point}
    {l : SymplecticQuadrangle.Line} (h : SymplecticQuadrangle.Incident p l) :
    incidenceWeight SymplecticQuadrangle.wEightCounts.incident p l = 1 := by
  have h' : SymplecticQuadrangle.wEightCounts.incident p l := h
  unfold incidenceWeight
  rw [if_pos h']

theorem incidenceWeight_wEight_eq_zero {p : SymplecticQuadrangle.Point}
    {l : SymplecticQuadrangle.Line} (h : ¬ SymplecticQuadrangle.Incident p l) :
    incidenceWeight SymplecticQuadrangle.wEightCounts.incident p l = 0 := by
  have h' : ¬ SymplecticQuadrangle.wEightCounts.incident p l := h
  unfold incidenceWeight
  rw [if_neg h']

/-- The coordinate membership relation of a `W8Table` is the algebraic
symplectic incidence relation.  This is the only use of the `incident_spec`
field. -/
theorem member_iff_incident {m : ℕ} (T : W8Table m) (x y : Fin 585) :
    member T.toTable x y = true ↔
      SymplecticQuadrangle.Incident (T.pointEquiv y)
        (T.lineEquiv (T.toTable.lambda x)) := by
  unfold member
  rw [T.incident_spec]
  constructor
  · intro hd
    exact of_decide_eq_true hd
  · intro hd
    exact decide_eq_true hd

/-- **The presentation link of a checked `W8Table` is the `W(8)` incidence
graph.**  Both bipartite classes and both cross terms are computed; nothing is
enumerated. -/
theorem wEight_adjacency_of_checkTable {m : ℕ} (T : W8Table m)
    (hcheck : checkTable T.toTable = true)
    (hbij : Function.Bijective T.toTable.lambda) (u v : Fin 585 × Bool) :
    (TriangularHodgeLayer.adjacencyCount (triangles T.toTable) u v : ℚ) =
      SymplecticQuadrangle.wEightQuadrangleLinkData.adj
        (wEightVertexEquiv T hbij u) (wEightVertexEquiv T hbij v) := by
  obtain ⟨x, s⟩ := u
  obtain ⟨y, t⟩ := v
  cases s with
  | false =>
      cases t with
      | false =>
          rw [wEightVertexEquiv_false, wEightVertexEquiv_false,
            wEight_adj_inl_inl, adjacencyCount_cast_false_false]
      | true =>
          rw [TriangularHodgeLayer.adjacencyCount_comm,
            adjacencyCount_of_checkTable T.toTable hcheck y x,
            wEightVertexEquiv_false, wEightVertexEquiv_true, wEight_adj_inl_inr]
          by_cases hI : SymplecticQuadrangle.Incident (T.pointEquiv x)
              (T.lineEquiv (T.toTable.lambda y))
          · rw [if_pos ((member_iff_incident T y x).mpr hI),
              incidenceWeight_wEight_eq_one hI]
          · rw [if_neg (fun hm => hI ((member_iff_incident T y x).mp hm)),
              incidenceWeight_wEight_eq_zero hI]
  | true =>
      cases t with
      | false =>
          rw [adjacencyCount_of_checkTable T.toTable hcheck x y,
            wEightVertexEquiv_true, wEightVertexEquiv_false, wEight_adj_inr_inl]
          by_cases hI : SymplecticQuadrangle.Incident (T.pointEquiv y)
              (T.lineEquiv (T.toTable.lambda x))
          · rw [if_pos ((member_iff_incident T x y).mpr hI),
              incidenceWeight_wEight_eq_one hI]
          · rw [if_neg (fun hm => hI ((member_iff_incident T x y).mp hm)),
              incidenceWeight_wEight_eq_zero hI]
      | true =>
          rw [wEightVertexEquiv_true, wEightVertexEquiv_true,
            wEight_adj_inr_inr, adjacencyCount_cast_true_true]

/-- **The link half of the verifier, with no second Boolean.**  A `W8Table`
passing `checkTable` identifies its presentation link with the algebraic
`W(8)` link data of `KazhdanHypSymplecticQuadrangleStrongRegular`. -/
noncomputable def linkIdentification_of_checkTable {m : ℕ} (T : W8Table m)
    (hcheck : checkTable T.toTable = true) :
    TriangleLinkIdentification (triangles T.toTable)
      SymplecticQuadrangle.wEightQuadrangleLinkData where
  vertexEquiv :=
    wEightVertexEquiv T (lambda_bijective_of_checkTable T.toTable hcheck)
  adjacency_eq :=
    wEight_adjacency_of_checkTable T hcheck
      (lambda_bijective_of_checkTable T.toTable hcheck)

end GQEightTableFormat
end KazhdanHyp
end GroupApproximation
