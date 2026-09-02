import GroupApproximation.GGT.KazhdanHypGirthEight
import GroupApproximation.GGT.KazhdanHypGQLinkTransfer
import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangleStrongRegular
import GroupApproximation.GGT.KazhdanHypGQTwoTable

/-!
# Compact finite verification of an unstructured triangle table

`Table n m` stores a point-to-line map and an `m`-row triangular table on
`Fin n`.  Its Boolean checker tests the local incidence conditions used by a
triangle presentation, then evaluates the exact finite `C(3)`--`T(8)`
predicate.  The incidence argument is a Boolean relation, so generated W(8)
data can use a compact coordinate evaluator; no 585 by 585 proof term is
required in the table format.

The direct girth clause is split from the local checker.  This keeps the
soundness theorem small and lets a generated verifier replace that clause by
chunked Boolean evaluations when a full `decide` reduction is too expensive.
The q=2 calibration reverses the published Kangaslampi--Vdovina rows, so the
checker uses the requested convention `y ∈ lambda(x)` while retaining the
same undirected presentation link.
-/

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

universe u

namespace GQEightTableFormat

/-- A triangular row with explicit fields, so generated array literals do not
depend on the parser's associativity for products. -/
structure Triple (n : ℕ) where
  x : Fin n
  y : Fin n
  z : Fin n
  deriving DecidableEq

/-- The compact finite data consumed by the Boolean verifier.  `incident p l`
means that point `p` lies on line `l`; `lambda x` is the line assigned to `x`.
Rows use the convention `y ∈ lambda(x)`, `z ∈ lambda(y)`, and
`x ∈ lambda(z)`. -/
structure Table (n m : ℕ) where
  incident : Fin n → Fin n → Bool
  lambda : Fin n → Fin n
  rows : Fin m → Triple n

def allFinN : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p 0 && allFinN n (fun i => p i.succ)

theorem allFinN_eq_true_iff (n : ℕ) (p : Fin n → Bool) :
    allFinN n p = true ↔ ∀ a, p a = true := by
  induction n with
  | zero => simp [allFinN]
  | succ n ih =>
      simp only [allFinN, Bool.and_eq_true]
      rw [Fin.forall_fin_succ, ih]

def allBool (p : Bool → Bool) : Bool := p false && p true

theorem allBool_eq_true_iff (p : Bool → Bool) :
    allBool p = true ↔ ∀ a, p a = true := by
  cases h0 : p false <;> cases h1 : p true <;>
    simp [allBool, h0, h1]

def allSigned {n : ℕ} (p : Fin n × Bool → Bool) : Bool :=
  allFinN n (fun i => allBool (fun s => p (i, s)))

theorem allSigned_eq_true_iff {n : ℕ} (p : Fin n × Bool → Bool) :
    allSigned p = true ↔ ∀ a, p a = true := by
  rw [allSigned, allFinN_eq_true_iff]
  constructor
  · intro h a
    exact (allBool_eq_true_iff _).mp (h a.1) a.2
  · intro h i
    exact (allBool_eq_true_iff _).mpr (fun s => h (i, s))

def triangles {n m : ℕ} (T : Table n m) :
    Fin m → TriangularHodgeLayer.Triangle (Fin n) :=
  fun j => ![((T.rows j).x, true), ((T.rows j).y, true),
    ((T.rows j).z, true)]

@[simp] theorem triangles_apply_zero {n m : ℕ} (T : Table n m) (j : Fin m) :
    (triangles T j 0) = ((T.rows j).x, true) := by
  rfl

@[simp] theorem triangles_apply_one {n m : ℕ} (T : Table n m) (j : Fin m) :
    (triangles T j 1) = ((T.rows j).y, true) := by
  rfl

@[simp] theorem triangles_apply_two {n m : ℕ} (T : Table n m) (j : Fin m) :
    (triangles T j 2) = ((T.rows j).z, true) := by
  rfl

/-- The Boolean form of `y ∈ lambda(x)`. -/
def member {n m : ℕ} (T : Table n m) (x y : Fin n) : Bool :=
  T.incident y (T.lambda x)

/-- The three local incidence requirements for one cyclic row. -/
def rowCompatible {n m : ℕ} (T : Table n m) (r : Triple n) : Bool :=
  member T r.x r.y && member T r.y r.z && member T r.z r.x

/-- A row contains a directed pair in one of its three cyclic positions. -/
def rowContainsPair {n : ℕ} (r : Triple n) (x y : Fin n) : Bool :=
  decide ((r.x = x ∧ r.y = y) ∨
    (r.y = x ∧ r.z = y) ∨ (r.z = x ∧ r.x = y))

/-- Number of rows containing a directed pair. -/
def pairCoverCount {n m : ℕ} (T : Table n m) (x y : Fin n) : ℕ :=
  ∑ j : Fin m, if rowContainsPair (T.rows j) x y = true then 1 else 0

/-- Exact cover of the compatible directed pairs. -/
def pairCoverCheck {n m : ℕ} (T : Table n m) : Bool :=
  allFinN n (fun x => allFinN n (fun y => decide
    (pairCoverCount T x y = if member T x y = true then 1 else 0)))

def lambdaCheck {n m : ℕ} (T : Table n m) : Bool :=
  decide (Function.Bijective T.lambda)

def rowCompatibilityCheck {n m : ℕ} (T : Table n m) : Bool :=
  allFinN m (fun j => rowCompatible T (T.rows j))

def noCubeCheck {n m : ℕ} (T : Table n m) : Bool :=
  allFinN m (fun j => decide
    (¬ ((T.rows j).x = (T.rows j).y ∧
      (T.rows j).y = (T.rows j).z)))

def positiveCardinalityCheck {n m : ℕ} (_T : Table n m) : Bool :=
  decide (0 < n)

/-- The exact link-agnostic girth check evaluated as a Boolean.  Generated
tables may replace this definition by a conjunction of vertex-index chunks;
the implication theorem below only uses its Boolean specification. -/
def positiveCheck {n m : ℕ} (T : Table n m) : Bool :=
  allFinN m (fun j => allFinN 3 (fun k =>
    decide ((triangles T j k).2 = true)))

def regularCheck {n m : ℕ} (T : Table n m) (d : ℕ) : Bool :=
  allSigned (fun u => decide
    (TriangularHodgeLayer.degree (triangles T) u = d))

def simpleCheck {n m : ℕ} (T : Table n m) : Bool :=
  allSigned (fun u => allSigned (fun v => decide
    (TriangularHodgeLayer.adjacencyCount (triangles T) u v ≤ 1)))

def commonNeighborCheck {n m : ℕ} (T : Table n m) : Bool :=
  allSigned (fun v => allSigned (fun v' =>
    if v = v' then true else decide
      ((∑ u, TriangularHodgeLayer.adjacencyCount (triangles T) u v *
        TriangularHodgeLayer.adjacencyCount (triangles T) u v') ≤ 1)))

def threePathCheck {n m : ℕ} (T : Table n m) : Bool :=
  allSigned (fun v => allSigned (fun v' =>
    if TriangularHodgeLayer.adjacencyCount (triangles T) v v' = 0 then
      decide ((∑ a, ∑ b,
        TriangularHodgeLayer.adjacencyCount (triangles T) v a *
        TriangularHodgeLayer.adjacencyCount (triangles T) a b *
        TriangularHodgeLayer.adjacencyCount (triangles T) b v') ≤ 1)
    else true))

def girthCheckAt {n m : ℕ} (T : Table n m) (d : ℕ) : Bool :=
  positiveCheck T && regularCheck T d && simpleCheck T &&
    commonNeighborCheck T && threePathCheck T

theorem positiveCheck_spec {n m : ℕ} (T : Table n m) :
    positiveCheck T = true ↔ ∀ j k, (triangles T j k).2 = true := by
  unfold positiveCheck
  rw [allFinN_eq_true_iff]
  constructor
  · intro h j
    exact (allFinN_eq_true_iff _ _).mp (h j)
  · intro h j
    exact (allFinN_eq_true_iff _ _).mpr
      (fun k => decide_eq_true_eq.mpr ((h j) k))

theorem regularCheck_spec {n m d : ℕ} (T : Table n m) :
    regularCheck T d = true ↔
      ∀ u, TriangularHodgeLayer.degree (triangles T) u = d := by
  unfold regularCheck
  rw [allSigned_eq_true_iff]
  exact ⟨fun h u => decide_eq_true_eq.mp (h u),
    fun h u => decide_eq_true_eq.mpr (h u)⟩

theorem simpleCheck_spec {n m : ℕ} (T : Table n m) :
    simpleCheck T = true ↔
      ∀ u v, TriangularHodgeLayer.adjacencyCount (triangles T) u v ≤ 1 := by
  unfold simpleCheck
  rw [allSigned_eq_true_iff]
  constructor
  · intro h u v
    exact decide_eq_true_eq.mp
      (((allSigned_eq_true_iff _).mp (h u)) v)
  · intro h u
    exact (allSigned_eq_true_iff _).mpr
      (fun v => decide_eq_true_eq.mpr (h u v))

theorem commonNeighborCheck_spec {n m : ℕ} (T : Table n m) :
    commonNeighborCheck T = true ↔
      ∀ v v', v ≠ v' →
        (∑ u, TriangularHodgeLayer.adjacencyCount (triangles T) u v *
          TriangularHodgeLayer.adjacencyCount (triangles T) u v') ≤ 1 := by
  unfold commonNeighborCheck
  rw [allSigned_eq_true_iff]
  constructor
  · intro h v v' hne
    have hh := ((allSigned_eq_true_iff _).mp (h v)) v'
    simp [hne] at hh
    exact hh
  · intro h v
    exact (allSigned_eq_true_iff _).mpr (fun v' => by
      by_cases hv : v = v'
      · simp [hv]
      · simp [hv, decide_eq_true_eq.mpr (h v v' hv)])

theorem threePathCheck_spec {n m : ℕ} (T : Table n m) :
    threePathCheck T = true ↔
      ∀ v v', TriangularHodgeLayer.adjacencyCount (triangles T) v v' = 0 →
        (∑ a, ∑ b,
          TriangularHodgeLayer.adjacencyCount (triangles T) v a *
          TriangularHodgeLayer.adjacencyCount (triangles T) a b *
          TriangularHodgeLayer.adjacencyCount (triangles T) b v') ≤ 1 := by
  unfold threePathCheck
  rw [allSigned_eq_true_iff]
  constructor
  · intro h v v' hzero
    have hh := ((allSigned_eq_true_iff _).mp (h v)) v'
    simp [hzero] at hh
    exact hh
  · intro h v
    exact (allSigned_eq_true_iff _).mpr (fun v' => by
      by_cases hv : TriangularHodgeLayer.adjacencyCount
          (triangles T) v v' = 0
      · simp [hv, decide_eq_true_eq.mpr (h v v' hv)]
      · simp [hv])

theorem girthCheckAt_eq_true_iff {n m d : ℕ} (T : Table n m) :
    girthCheckAt T d = true ↔ GirthEightChecks (triangles T) d := by
  simp only [girthCheckAt, Bool.and_eq_true, positiveCheck_spec,
    regularCheck_spec, simpleCheck_spec, commonNeighborCheck_spec,
    threePathCheck_spec, GirthEightChecks, and_assoc]

def localCheck {n m : ℕ} (T : Table n m) : Bool :=
  positiveCardinalityCheck T && lambdaCheck T &&
    rowCompatibilityCheck T && pairCoverCheck T && noCubeCheck T

/-- Boolean verifier for a degree-`d` table. -/
def checkTableAt {n m : ℕ} (T : Table n m) (d : ℕ) : Bool :=
  localCheck T && girthCheckAt T d

/-- The W(8) verifier requested by the search pipeline. -/
def checkTable {n m : ℕ} (T : Table n m) : Bool :=
  checkTableAt T 9

theorem checkTableAt_true_girth {n m d : ℕ} (T : Table n m)
    (h : checkTableAt T d = true) :
    GirthEightChecks (triangles T) d := by
  rw [checkTableAt, Bool.and_eq_true] at h
  exact (girthCheckAt_eq_true_iff T).mp h.2

theorem checkTable_true_girth {n m : ℕ} (T : Table n m)
    (h : checkTable T = true) :
    GirthEightChecks (triangles T) 9 := by
  exact checkTableAt_true_girth T h

theorem checkTableAt_true_local {n m d : ℕ} (T : Table n m)
    (h : checkTableAt T d = true) : localCheck T = true := by
  rw [checkTableAt, Bool.and_eq_true] at h
  exact h.1

/-! ## W(8) coordinate package -/

open SymplecticQuadrangle

/-- A W(8) table additionally supplies the finite coordinate enumerations.
`incident_spec` ties the compact Boolean relation to the already proved
symplectic incidence predicate. -/
structure W8Table (m : ℕ) extends Table 585 m where
  pointEquiv : Fin 585 ≃ SymplecticQuadrangle.Point
  lineEquiv : Fin 585 ≃ SymplecticQuadrangle.Line
  incident_spec : ∀ p l,
    toTable.incident p l =
      decide (SymplecticQuadrangle.Incident (pointEquiv p) (lineEquiv l))

noncomputable def lambdaEquiv {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda) : Fin 585 ≃ Fin 585 :=
  Equiv.ofBijective T.toTable.lambda h

/-- The signed-link equivalence for the requested successor convention.  A
positive signed generator is sent to its assigned line and a negative one to
the corresponding point, so `y ∈ lambda(x)` is exactly a cross-part edge. -/
noncomputable def wEightVertexEquiv {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda) :
    (Fin 585 × Bool) ≃
      (SymplecticQuadrangle.Point ⊕ SymplecticQuadrangle.Line) := by
  let eLine := lambdaEquiv T h
  let P := T.pointEquiv
  let L := T.lineEquiv
  refine {
    toFun := fun u => match u.2 with
      | true => Sum.inr (L (T.toTable.lambda u.1))
      | false => Sum.inl (P u.1)
    invFun := fun v => match v with
      | Sum.inl p => (P.symm p, false)
      | Sum.inr l => (eLine.symm (L.symm l), true)
    left_inv := ?_
    right_inv := ?_ }
  · intro u
    rcases u with ⟨u, s⟩
    cases s
    · dsimp
      apply Prod.ext
      · exact P.left_inv u
      · rfl
    · dsimp
      apply Prod.ext
      · change eLine.symm (L.symm (L (T.toTable.lambda u))) = u
        rw [L.symm_apply_apply]
        exact eLine.left_inv u
      · rfl
  · intro v
    cases v with
    | inl p =>
        change Sum.inl (P (P.symm p)) = Sum.inl p
        rw [P.apply_symm_apply]
    | inr l =>
        change Sum.inr (L (T.lambda (eLine.symm (L.symm l)))) = Sum.inr l
        congr 1
        change L (eLine (eLine.symm (L.symm l))) = l
        rw [eLine.apply_symm_apply, L.apply_symm_apply]

/-- Direct Boolean adjacency agreement with the algebraic W(8) link.  This is
the final small check emitted with a witness when the full link equality is
not reduced by a single kernel `decide`. -/
noncomputable def wEightLinkCheck {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda) : Bool :=
  decide (∀ u v,
    (TriangularHodgeLayer.adjacencyCount (triangles T.toTable) u v : ℚ) =
      (_root_.GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData).adj
        (wEightVertexEquiv T h u) (wEightVertexEquiv T h v))

noncomputable def checkW8Table {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda) : Bool :=
  checkTable T.toTable && wEightLinkCheck T h

theorem checkW8Table_true_girth {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda)
    (hc : checkW8Table T h = true) :
    GirthEightChecks (triangles T.toTable) 9 := by
  rw [checkW8Table, Bool.and_eq_true] at hc
  exact checkTable_true_girth T.toTable hc.1

noncomputable def checkW8Table_true_link {m : ℕ} (T : W8Table m)
    (h : Function.Bijective T.toTable.lambda)
    (hc : checkW8Table T h = true) :
    TriangleLinkIdentification (triangles T.toTable)
      (_root_.GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData) := by
  rw [checkW8Table, Bool.and_eq_true] at hc
  refine {
    vertexEquiv := wEightVertexEquiv T h
    adjacency_eq := ?_ }
  exact decide_eq_true_eq.mp hc.2

/-! ## q=2 end-to-end calibration -/

def qTwoRows : Fin 15 → Triple 15 := fun j => {
  x := (GQTwoTable.triangles j 0).1
  y := (GQTwoTable.triangles j 1).1
  z := (GQTwoTable.triangles j 2).1 }

def qTwoData : Table 15 15 := {
  incident := fun p l => decide (GQTwoTable.incidence l p = 1)
  lambda := id
  rows := qTwoRows }

theorem qTwoData_lambda_bijective :
    Function.Bijective qTwoData.lambda := by
  exact Function.bijective_id

theorem qTwoTriangles_eq :
    triangles qTwoData = GQTwoTable.triangles := by
  funext j k
  fin_cases k
  · change ((GQTwoTable.triangles j 0).1, true) = GQTwoTable.triangles j 0
    rcases h : GQTwoTable.triangles j 0 with ⟨g, s⟩
    have hs : s = true := by simpa [h] using GQTwoTable.positive j 0
    simp [hs]
  · change ((GQTwoTable.triangles j 1).1, true) = GQTwoTable.triangles j 1
    rcases h : GQTwoTable.triangles j 1 with ⟨g, s⟩
    have hs : s = true := by simpa [h] using GQTwoTable.positive j 1
    simp [hs]
  · change ((GQTwoTable.triangles j 2).1, true) = GQTwoTable.triangles j 2
    rcases h : GQTwoTable.triangles j 2 with ⟨g, s⟩
    have hs : s = true := by simpa [h] using GQTwoTable.positive j 2
    simp [hs]

theorem qTwoData_checkTableAt :
    checkTableAt qTwoData 3 = true := by
  decide

theorem qTwoData_girth :
    GirthEightChecks (triangles qTwoData) 3 :=
  checkTableAt_true_girth qTwoData qTwoData_checkTableAt

theorem emptyTable_checkTableAt_false :
    checkTableAt (Table.mk (n := 0) (m := 0)
      (fun _ _ => false) (fun x => x) (fun j => nomatch j)) 9 = false := by
  decide

end GQEightTableFormat
end KazhdanHyp
end GroupApproximation
