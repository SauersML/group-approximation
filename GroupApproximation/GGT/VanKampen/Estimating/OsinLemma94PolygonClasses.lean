import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BudgetFilter
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the sides of a polygon in classes

Osin (math/0411039v3, §9), proof of Lemma 9.4: "Let `S_i` denote the sum of lengths of all arcs
of type (A1) in `∂Δ_i`, `i = 1, …, d`."  "The boundary of `Δ̃_i` decomposes into `k_i`
subpaths, each of which is either `t_j^{±1}` for some `j = 1, …, l`, or an arc".  In
`OsinLemma94RealizedPolygons` the sides are pieces of the face walk of `S.diagram`.  The walk can
leave a relator cell through a hair or a bubble and come back to it, so one arc of Osin can be
several sides.  This module joins consecutive sides along one cell, or along one section of
`∂Δ`, into classes.

* `OsinLemma94ClassPolygons P`: the sides of each polygon, read cyclically from `classBase`,
  split into runs of consecutive sides, the classes.  A class of kind `cell j` is one reversed
  arc of the `j`-th relator cell, and a class of kind `boundary j` one arc of section `j`, with
  the gaps between consecutive sides included.  A gap is a closed path, so its word has value
  one.  A cutting class and a short class are single sides.
* `relatorClasses`: the (A1) classes of the polygons with at least two classes.  A polygon with
  one class is a one-sided bubble.  Its word has value one, so by
  `IsLambdaCQuasiGeodesicWord.le_ceil_of_listVal_eq_one` it has at most `⌈(c + 2) / λ⌉₊`
  letters, and it is counted in the slack.
* `ClassBudget`: `∑ k_i ≤ K n`, summed over the polygons with an (A1) class and at least two
  classes.
* `ClassCovers M L`: `S ≤ M ∑ S_i + L n`, where `S_i` sums the (A1) class words.
* `unbound_lt_of_classes`: the contradiction at fixed parameters, over the classes, with the
  class polygons dense at `⌊ρ / (4 M²)⌋`.
* `OsinLemma94ClassCountInput`: the count piece over the classes, with `K`, `M` and `L` chosen
  after `ε`, under clause (b) of Lemma 9.7 below the number of relator cells.
* `ofSides`: model test, every side its own class.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **The sides of a component polygon in classes.**

Read from side `classBase k`, the sides of polygon `k` split into `classCount k` runs of
consecutive sides.  `gap k s` is the path across the gap after side `s`: along the cell for a
`cell` class, along `∂Δ` for a `boundary` class.  The darts of a class are its sides with the gaps
between them.  A class of kind `cell j` is one arc of the `j`-th relator cell, read from across,
and a class of kind `boundary j` is one arc of `∂Δ` inside section `j`. -/
structure OsinLemma94ClassPolygons {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) where
  /-- The number of classes of polygon `k`. -/
  classCount : Fin P.count → ℕ
  /-- The side where class `0` starts. -/
  classBase : Fin P.count → ℕ
  /-- The sides of class `i` of polygon `k`, in walk order. -/
  classSides : Fin P.count → ℕ → List ℕ
  /-- The classes, read in order, are the sides read cyclically from `classBase k`. -/
  sides_eq : ∀ k, (List.range (classCount k)).flatMap (classSides k) =
    (List.range (P.sideCount k)).rotate (classBase k)
  classSides_ne_nil : ∀ k i, i < classCount k → classSides k i ≠ []
  /-- The kind of class `i` of polygon `k`. -/
  classKind : Fin P.count → ℕ → OsinLemma94SideClass S.diagram.rCellCount
  kind_eq : ∀ k i, i < classCount k → ∀ s ∈ classSides k i, P.kind k s = classKind k i
  /-- A cutting class and a short class are single sides. -/
  single : ∀ k i, i < classCount k → (classKind k i = .cutting ∨ classKind k i = .short) →
    (classSides k i).length = 1
  /-- The darts across the gap after side `s`. -/
  gap : Fin P.count → ℕ → List S.diagram.toCombMap.Dart
  /-- A gap is a closed path: its word has value one. -/
  gap_value : ∀ k i, i < classCount k → ∀ s ∈ classSides k i,
    RelLetter.listVal (Embedded.dartWord S.diagram (gap k s)) = 1
  /-- A class ends with a side, not with a gap. -/
  gap_last : ∀ k i, i < classCount k → ∀ s ∈ (classSides k i).getLast?, gap k s = []
  /-- Type (A1): the class, gaps included, is one arc of the `j`-th relator cell, read from
  across. -/
  cell_arc : ∀ k i (j : Fin S.diagram.rCellCount), i < classCount k → classKind k i = .cell j →
    ∃ arc : Embedded.CyclicArc (Embedded.cellDarts S.diagram j),
      ((classSides k i).flatMap fun s => P.sideDarts k s ++ gap k s) = arc.reverseDarts
  /-- Type (A2): the class, gaps included, is one arc of `∂Δ` inside section `j`. -/
  boundary_arc : ∀ k i (j : ℕ), i < classCount k → classKind k i = .boundary j →
    ∃ hj : j < cuts.count, ∃ arc : Embedded.CyclicArc (Embedded.targetDarts S.diagram none),
      ((classSides k i).flatMap fun s => P.sideDarts k s ++ gap k s) = arc.darts ∧
        cuts.cut ⟨j, by omega⟩ ≤ arc.start.1 ∧
          arc.start.1 + arc.length ≤ cuts.cut ⟨j + 1, by omega⟩
  /-- (A1) and (A2) class words and cutting paths are `(λ, c + 2)`-quasi-geodesic over the
  symmetric label alphabet. -/
  quasiGeodesic : ∀ k i, i < classCount k → classKind k i ≠ .short →
    IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2)
      (Embedded.dartWord S.diagram
        ((classSides k i).flatMap fun s => P.sideDarts k s ++ gap k s))

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- The darts of class `i` of polygon `k`: its sides, with the gaps between them. -/
def classDarts (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    List S.diagram.toCombMap.Dart :=
  (Q.classSides k i).flatMap fun s => P.sideDarts k s ++ Q.gap k s

/-- The word of class `i` of polygon `k`: the labels of its darts. -/
def word (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    List (RelLetter G Lambda) :=
  Embedded.dartWord S.diagram (Q.classDarts k i)

/-- The corner of polygon `k` before class `i`. -/
def corner (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) : G :=
  RelLetter.listVal ((List.range i).flatMap (Q.word k))

/-- The class `N1`: the (A1) classes of a polygon with at least two classes. -/
def relatorClasses (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) : Set ℕ :=
  {i | 2 ≤ Q.classCount k ∧ ∃ j, Q.classKind k i = .cell j}

/-- The classes `N1 ∪ N2`: all classes but those of type (A3). -/
def longClasses (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) : Set ℕ :=
  {i | Q.classKind k i ≠ .short}

open Classical in
/-- The polygons with an (A1) class and at least two classes. -/
noncomputable def budgetPolygons (Q : OsinLemma94ClassPolygons P) : Finset (Fin P.count) :=
  Finset.univ.filter fun k =>
    2 ≤ Q.classCount k ∧ ∃ i < Q.classCount k, ∃ j, Q.classKind k i = .cell j

/-- **The class budget.**  Lemma 9.3, "`∑ n_i ≤ 53 n`", and (38), "`k_i ≤ 4 n_i`", as one class
constant, summed over the polygons with an (A1) class and at least two classes. -/
def ClassBudget (Q : OsinLemma94ClassPolygons P) (K : ℕ) : Prop :=
  ∑ k ∈ Q.budgetPolygons, Q.classCount k ≤ K * Delta.rCellCount

/-- **The class cover.**  `S ≤ M ∑ S_i + L n`: the unbound darts are covered by the (A1)
class words of the polygons with at least two classes, `M` times over, except for at most
`L n` of them.  An unbound stretch of a cell with its own cell across is bounded only through
quasi-geodesicity, at most `⌈1 / λ⌉₊` times the other unbound darts next to it, so the factor
`M` sits on the class words. -/
def ClassCovers (Q : OsinLemma94ClassPolygons P) (M L : ℕ) : Prop :=
  (∑ i : Fin S.diagram.rCellCount, ((RegionCandidate.unboundDarts S.family i).card : ℝ)) ≤
    (M : ℝ) * ∑ k, classWordLength (Q.word k) (Q.classCount k) (Q.relatorClasses k) +
      (L : ℝ) * Delta.rCellCount

/-- **Model test: the fields are consistent.**  Every side is its own class, with no gaps. -/
def ofSides (P : OsinLemma94RealizedPolygons S) : OsinLemma94ClassPolygons P where
  classCount := P.sideCount
  classBase := fun _ => 0
  classSides := fun _ i => [i]
  sides_eq := by
    intro k
    simp only [List.rotate_zero, List.flatMap_singleton']
  classSides_ne_nil := fun _ i _ => List.cons_ne_nil i []
  classKind := P.kind
  kind_eq := by
    intro k i _ s hs
    obtain rfl := List.mem_singleton.mp hs
    rfl
  single := fun _ _ _ _ => rfl
  gap := fun _ _ => []
  gap_value := fun _ _ _ _ _ => RelLetter.listVal_nil
  gap_last := fun _ _ _ _ _ => rfl
  cell_arc := by
    intro k i j hi hj
    simp only [List.flatMap_singleton, List.append_nil]
    exact P.cell_arc k i j hi hj
  boundary_arc := by
    intro k i j hi hj
    simp only [List.flatMap_singleton, List.append_nil]
    exact P.boundary_arc k i j hi hj
  quasiGeodesic := by
    intro k i hi hne
    simp only [List.flatMap_singleton, List.append_nil]
    exact P.quasiGeodesic k i hi hne

/-- A class word is its side words with the gap words between them. -/
theorem word_eq (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    Q.word k i = (Q.classSides k i).flatMap
      fun s => P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) := by
  simp only [OsinLemma94ClassPolygons.word, OsinLemma94ClassPolygons.classDarts,
    OsinLemma94RealizedPolygons.word, Embedded.dartWord, List.map_flatMap, List.map_append]

/-- The class words, read in order, are the side words read from `classBase k`, with the
gaps. -/
theorem flatMap_word (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    (List.range (Q.classCount k)).flatMap (Q.word k) =
      ((List.range (P.sideCount k)).rotate (Q.classBase k)).flatMap
        fun s => P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) := by
  rw [← Q.sides_eq k, List.flatMap_assoc]
  exact congrArg (fun f => (List.range (Q.classCount k)).flatMap f) (funext (Q.word_eq k))

/-- Every side of a class is a side of the polygon. -/
theorem lt_sideCount_of_mem (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ)
    (hi : i < Q.classCount k) (s : ℕ) (hs : s ∈ Q.classSides k i) : s < P.sideCount k := by
  have hmem : s ∈ (List.range (Q.classCount k)).flatMap (Q.classSides k) :=
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hs⟩
  rw [Q.sides_eq k, List.mem_rotate, List.mem_range] at hmem
  exact hmem

/-- A class of one side `s` has the word of side `s`. -/
theorem word_eq_of_eq_singleton (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ)
    (hi : i < Q.classCount k) {s : ℕ} (hs : Q.classSides k i = [s]) :
    Q.word k i = P.word k s := by
  have hgap : Q.gap k s = [] :=
    Q.gap_last k i hi s (Option.mem_def.mpr (by rw [hs, List.getLast?_singleton]))
  rw [Q.word_eq, hs, List.flatMap_singleton, hgap]
  exact List.append_nil _

/-- Gap words of value one do not change the value. -/
theorem listVal_flatMap_append (l : List ℕ) (w g : ℕ → List (RelLetter G Lambda))
    (hg : ∀ s ∈ l, RelLetter.listVal (g s) = 1) :
    RelLetter.listVal (l.flatMap fun s => w s ++ g s) = RelLetter.listVal (l.flatMap w) := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [List.flatMap_cons, HullSC.RelWord.listVal_append, hg s List.mem_cons_self,
      mul_one]
    rw [ih fun t ht => hg t (List.mem_cons_of_mem s ht)]

/-- A cyclic reading of a product of value one has value one. -/
theorem listVal_flatMap_rotate (l : List ℕ) (w : ℕ → List (RelLetter G Lambda)) (b : ℕ)
    (h : RelLetter.listVal (l.flatMap w) = 1) :
    RelLetter.listVal ((l.rotate b).flatMap w) = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, List.flatMap_append, HullSC.RelWord.listVal_append]
  rw [← List.take_append_drop (b % l.length) l, List.flatMap_append,
    HullSC.RelWord.listVal_append] at h
  exact mul_eq_one_comm.mp h

theorem corner_step (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    Q.corner k (i + 1) = Q.corner k i * RelLetter.listVal (Q.word k i) := by
  unfold corner
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
    HullSC.RelWord.listVal_append]

/-- **The class polygon closes up.**  The side words close up (`P.closed`), the gaps have value
one, and a cyclic reading of a closed word is closed. -/
theorem corner_closed (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    Q.corner k (Q.classCount k) = Q.corner k 0 := by
  unfold corner
  rw [List.range_zero, List.flatMap_nil, RelLetter.listVal_nil, Q.flatMap_word k,
    listVal_flatMap_append]
  · exact listVal_flatMap_rotate _ (P.word k) (Q.classBase k) (P.closed k)
  · intro s hs
    rw [← Q.sides_eq k, List.mem_flatMap] at hs
    obtain ⟨i, hi, hsi⟩ := hs
    exact Q.gap_value k i (List.mem_range.mp hi) s hsi

theorem quasiGeodesic_of_mem (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ)
    (hi : i < Q.classCount k) (hmem : i ∈ Q.relatorClasses k ∨ i ∈ Q.longClasses k) :
    IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2) (Q.word k i) := by
  refine Q.quasiGeodesic k i hi ?_
  rcases hmem with hcell | hlong
  · obtain ⟨-, j, hj⟩ : 2 ≤ Q.classCount k ∧ ∃ j, Q.classKind k i = .cell j := hcell
    rw [hj]
    intro h
    cases h
  · exact hlong

/-- A short class is one short side, so its word is admissible and at most `ε` long. -/
theorem short_of_not_mem (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ)
    (hi : i < Q.classCount k) (hnot : i ∉ Q.longClasses k) :
    HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i) ∧
      (Q.word k i).length ≤ eps := by
  have hshort : Q.classKind k i = .short := by
    by_contra hne
    exact hnot hne
  obtain ⟨s, hs⟩ := List.length_eq_one_iff.mp (Q.single k i hi (Or.inr hshort))
  have hmem : s ∈ Q.classSides k i := by
    rw [hs]
    exact List.mem_singleton_self s
  rw [Q.word_eq_of_eq_singleton k i hi hs]
  exact P.short k s (Q.lt_sideCount_of_mem k i hi s hmem)
    ((Q.kind_eq k i hi s hmem).trans hshort)

open Classical in
/-- A polygon with a class in `N1` is in the class budget. -/
theorem mem_budgetPolygons (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ)
    (hi : i < Q.classCount k) (hmem : i ∈ Q.relatorClasses k) : k ∈ Q.budgetPolygons := by
  obtain ⟨h2, j, hj⟩ : 2 ≤ Q.classCount k ∧ ∃ j, Q.classKind k i = .cell j := hmem
  unfold budgetPolygons
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ k, h2, i, hi, j, hj⟩

/-- **The slack and the factor cost `2 M`.**  If `n √ρ ≤ S ≤ M ∑ S_i + L n`, `M > 0` and
`ρ ≥ 4 L²`, then the class polygons are dense at `⌊ρ / (4 M²)⌋`. -/
theorem dense_of_classCovers (Q : OsinLemma94ClassPolygons P) {M L rho : ℕ}
    (hcovers : Q.ClassCovers M L) (hM : 0 < M) (hL : 4 * L * L ≤ rho)
    (hge : (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) ≤
      ∑ i : Fin S.diagram.rCellCount, ((RegionCandidate.unboundDarts S.family i).card : ℝ)) :
    (Delta.rCellCount : ℝ) * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ) ≤
      ∑ k, classWordLength (Q.word k) (Q.classCount k) (Q.relatorClasses k) := by
  have hrho : (4 : ℝ) * L * L ≤ rho := by exact_mod_cast hL
  have hquarter : (4 : ℝ) * M * M * ((rho / (4 * M * M) : ℕ) : ℝ) ≤ rho := by
    have h4 : 4 * M * M * (rho / (4 * M * M)) ≤ rho := Nat.mul_div_le rho (4 * M * M)
    exact_mod_cast h4
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hL0 : (0 : ℝ) ≤ 2 * (L : ℝ) := by positivity
  have hrho0 : (0 : ℝ) ≤ (rho : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ ((rho / (4 * M * M) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ 2 * M * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ) := by positivity
  have hn0 : (0 : ℝ) ≤ (Delta.rCellCount : ℝ) := Nat.cast_nonneg _
  have hsqrtL : 2 * (L : ℝ) ≤ Real.sqrt (rho : ℝ) := by
    rw [Real.le_sqrt hL0 hrho0]
    nlinarith
  have hsqrtQ : 2 * M * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ) ≤ Real.sqrt (rho : ℝ) := by
    rw [Real.le_sqrt hQ0 hrho0, mul_pow, mul_pow, Real.sq_sqrt hm0]
    nlinarith
  have hstep : M * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ) ≤ Real.sqrt (rho : ℝ) - L := by
    linarith
  have hn := mul_le_mul_of_nonneg_left hstep hn0
  rw [mul_sub] at hn
  unfold ClassCovers at hcovers
  have hmul : (M : ℝ) * ((Delta.rCellCount : ℝ) * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ)) ≤
      M * ∑ k, classWordLength (Q.word k) (Q.classCount k) (Q.relatorClasses k) := by
    linarith
  exact le_of_mul_le_mul_left hmul hM0

/-- **The contradiction at fixed parameters, over the classes.**  "Assume that `S ≥ n √ρ`."
The class polygons are dense at `⌊ρ / (4 M²)⌋`.  The polygons outside the class budget have no
class in `N1`, so the metric half applies to the budgeted polygons alone and gives a backwards
connector pair on class words, which the cases refute. -/
theorem unbound_lt_of_classes (Q : OsinLemma94ClassPolygons P) {K M L rho rhom : ℕ}
    (hcells : 0 < Delta.rCellCount) (hbudget : Q.ClassBudget K) (hcovers : Q.ClassCovers M L)
    (hM : 0 < M) (hrhom : 4 * M * M * rhom ≤ rho) (hL : 4 * L * L ≤ rho)
    (hmetric : ∀ rho' : ℕ, rhom ≤ rho' →
      OsinLemma94DensePolygonsAntiparallel (symmetricLabelAlphabet D) lambda (c + 2) eps rho' K)
    (hcases : ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k)
      (Q.word k) (Q.classCount k) (Q.relatorClasses k) (Q.longClasses k) eps),
        C.b' < C.b → False) :
    (∑ i : Fin S.diagram.rCellCount,
        ((RegionCandidate.unboundDarts S.family i).card : ℝ)) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := by
  by_contra hge
  have hdense := Q.dense_of_classCovers hcovers hM hL (not_lt.mp hge)
  have hle : rhom ≤ rho / (4 * M * M) := by
    refine (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos (by norm_num) hM) hM)).mpr ?_
    rw [Nat.mul_comm]
    exact hrhom
  obtain ⟨k, C, hback⟩ := OsinLemma94DensePolygonsAntiparallel.exists_of_budget_on
    (hmetric (rho / (4 * M * M)) hle) hcells Q.classCount Q.corner Q.word Q.relatorClasses
    Q.longClasses Q.budgetPolygons Q.mem_budgetPolygons hbudget Q.corner_closed
    (fun k i _ => Q.corner_step k i) Q.quasiGeodesic_of_mem Q.short_of_not_mem hdense
  exact hcases k C hback

end OsinLemma94ClassPolygons

/-- **Count piece of Lemma 9.4, over the classes.**  Lemma 9.3, "`∑ n_i ≤ 53 n`", and (38),
"`k_i ≤ 4 n_i`", as one class constant `K` chosen after `ε`, over the polygons with an (A1) class
and at least two classes.  With it, `S ≤ M ∑ S_i + L n`, where `S_i` sums the (A1) class words
of those polygons and `M > 0` and `L` are also chosen after `ε`.  The factor `M` pays for the
unbound stretches with their own cell across.  The slack `L n` leaves room for the unbound darts
along selected regions and for the value-one arcs at the class ends and the region ends.
Clause (b) of Lemma 9.7 below the number of relator cells of `Δ` is a hypothesis, used against a
pocket with relator cells behind an edge with one cell on both sides. -/
def OsinLemma94ClassCountInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K M L : ℕ, 0 < M ∧ ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∃ Q : OsinLemma94ClassPolygons P, Q.ClassBudget K ∧ Q.ClassCovers M L

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.word_eq
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.flatMap_word
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.lt_sideCount_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.word_eq_of_eq_singleton
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.listVal_flatMap_append
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.listVal_flatMap_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.corner_step
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.corner_closed
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.quasiGeodesic_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.short_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.mem_budgetPolygons
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.dense_of_classCovers
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.unbound_lt_of_classes

end GroupApproximation.GGT.VanKampen
