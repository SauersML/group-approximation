import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassTransitions
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the junctions of the class producer

Osin (math/0411039v3, §9), proof of Lemma 9.4: "The boundary of `Δ̃_i` decomposes into `k_i`
subpaths".  The classes of `OsinLemma94ClassPolygons` are runs of consecutive sides that join
(`CyclicRuns`).  This module fixes the join predicate and the gap across a junction.

Let side `s` of polygon `k` end with the dart `e`, and let side `s + 1` start with `e'`.
* Two sides on one relator cell (kind `cell j`): along the cell, `a = α e'` reaches `b = α e` after
  `m + 1` face steps, with `m` least.  The gap is `α (facePerm^m a), …, α (facePerm a)`
  (`ClassProducer.cellGapOf`).
* Two sides on one section (kind `boundary j`): the gap is the stretch of `∂Δ` strictly between
  them (`ClassProducer.boundaryGapOf`).
* `OsinLemma94RealizedPolygons.ClassJoins P k s`: the sides join at kind level (`KindJoins`), the gap
  reads a word of value one, a same-cell gap has no dart on the polygon face, and a same-section
  junction moves forward along `∂Δ`.
* `OsinLemma94RealizedPolygons.badJunctions P k`: the kind-level joins that are not class joins.
* `ClassProducer.isChain_append_cellGapOf`: a gap links two reversed cell walks into one.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace ClassProducer

variable {M : CombMap.{v}}

open Classical in
/-- The gap of a same-cell junction from `a` to `b`: with `m` least such that
`facePerm^(m + 1) a = b`, the darts `α (facePerm^m a), …, α (facePerm a)`. -/
noncomputable def cellGapOf (M : CombMap.{v}) (a b : M.Dart) : List M.Dart :=
  if h : ∃ m, (M.facePerm ^ (m + 1)) a = b then
    ((List.range (Nat.find h)).map fun t => M.alpha ((M.facePerm ^ (t + 1)) a)).reverse
  else []

open Classical in
/-- The entries of `l` strictly between the entries `e` and `e'`. -/
noncomputable def boundaryGapOf {α : Type*} (l : List α) (e e' : α) : List α :=
  (l.drop (l.idxOf e + 1)).take (l.idxOf e' - (l.idxOf e + 1))

/-- `y` comes before `x` along the face across: `facePerm (α y) = α x`.  A reversed cell arc is a
`Backward` chain. -/
def Backward (M : CombMap.{v}) (x y : M.Dart) : Prop :=
  M.facePerm (M.alpha y) = M.alpha x

open scoped Classical

theorem cellGapOf_eq_nil {a b : M.Dart} (h : ∃ m, (M.facePerm ^ (m + 1)) a = b)
    (hm : Nat.find h = 0) : cellGapOf M a b = [] := by
  rw [cellGapOf, dif_pos h, hm]
  simp only [List.range_zero, List.map_nil, List.reverse_nil]

theorem head?_cellGapOf {a b : M.Dart} (h : ∃ m, (M.facePerm ^ (m + 1)) a = b) {m : ℕ}
    (hm : Nat.find h = m + 1) :
    (cellGapOf M a b).head? = some (M.alpha ((M.facePerm ^ (m + 1)) a)) := by
  rw [cellGapOf, dif_pos h, hm, List.head?_reverse, List.range_succ, List.map_append,
    List.getLast?_append]
  simp

theorem getLast?_cellGapOf {a b : M.Dart} (h : ∃ m, (M.facePerm ^ (m + 1)) a = b) {m : ℕ}
    (hm : Nat.find h = m + 1) :
    (cellGapOf M a b).getLast? = some (M.alpha (M.facePerm a)) := by
  rw [cellGapOf, dif_pos h, hm, List.getLast?_reverse, List.range_succ_eq_map, List.map_cons]
  simp

/-- A same-cell gap is a reversed cell walk. -/
theorem isChain_cellGapOf (a b : M.Dart) : (cellGapOf M a b).IsChain (Backward M) := by
  have hinv : ∀ x, M.alpha (M.alpha x) = x := M.alpha_involutive
  unfold cellGapOf
  split_ifs with h
  · rw [List.isChain_reverse, List.isChain_map, List.isChain_iff_getElem]
    intro i hi
    rw [List.getElem_range, List.getElem_range]
    show M.facePerm (M.alpha (M.alpha _)) = M.alpha (M.alpha _)
    rw [hinv, hinv, pow_succ' M.facePerm (i + 1), Equiv.Perm.mul_apply]
  · exact List.IsChain.nil

/-- **A gap links two reversed cell walks.**  If `l₁` ends with `e`, `l₂` starts with `e'`, and
`α e'` reaches `α e` along the cell, then `l₁`, the gap and `l₂` form one reversed cell walk. -/
theorem isChain_append_cellGapOf {l₁ l₂ : List M.Dart} {e e' : M.Dart}
    (h₁ : l₁.IsChain (Backward M)) (h₂ : l₂.IsChain (Backward M))
    (he : l₁.getLast? = some e) (he' : l₂.head? = some e')
    (h : ∃ m, (M.facePerm ^ (m + 1)) (M.alpha e') = M.alpha e) :
    (l₁ ++ cellGapOf M (M.alpha e') (M.alpha e) ++ l₂).IsChain (Backward M) := by
  have hinv : ∀ x, M.alpha (M.alpha x) = x := M.alpha_involutive
  have hspec := Nat.find_spec h
  rcases hm : Nat.find h with _ | m
  · rw [cellGapOf_eq_nil h hm, List.append_nil]
    refine List.isChain_append.mpr ⟨h₁, h₂, fun x hx y hy => ?_⟩
    obtain rfl : e = x := Option.some_inj.mp (he.symm.trans (Option.mem_def.mp hx))
    obtain rfl : e' = y := Option.some_inj.mp (he'.symm.trans (Option.mem_def.mp hy))
    rw [hm, zero_add, pow_one] at hspec
    exact hspec
  · rw [hm] at hspec
    refine List.isChain_append.mpr
      ⟨List.isChain_append.mpr ⟨h₁, isChain_cellGapOf _ _, fun x hx y hy => ?_⟩, h₂,
        fun x hx y hy => ?_⟩
    · obtain rfl : e = x := Option.some_inj.mp (he.symm.trans (Option.mem_def.mp hx))
      rw [head?_cellGapOf h hm, Option.mem_def, Option.some_inj] at hy
      subst hy
      show M.facePerm (M.alpha (M.alpha _)) = M.alpha e
      rw [hinv, show M.facePerm ((M.facePerm ^ (m + 1)) (M.alpha e')) =
          (M.facePerm ^ (m + 1 + 1)) (M.alpha e') by
        rw [pow_succ' M.facePerm (m + 1), Equiv.Perm.mul_apply]]
      exact hspec
    · rw [List.getLast?_append, getLast?_cellGapOf h hm, Option.mem_def] at hx
      simp only [Option.some_or, Option.some_inj] at hx
      obtain rfl : e' = y := Option.some_inj.mp (he'.symm.trans (Option.mem_def.mp hy))
      subst hx
      show M.facePerm (M.alpha e') = M.alpha (M.alpha (M.facePerm (M.alpha e')))
      rw [hinv]

end ClassProducer

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The gap after side `s` of polygon `k`**: a same-cell gap, a stretch of `∂Δ`, or nothing. -/
noncomputable def junctionGap (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ) :
    List S.diagram.toCombMap.Dart :=
  match (P.sideDarts k s).getLast?, (P.sideDarts k ((s + 1) % P.sideCount k)).head?,
      P.kind k s with
  | some e, some e', .cell _ =>
      ClassProducer.cellGapOf S.diagram.toCombMap (S.diagram.toCombMap.alpha e')
        (S.diagram.toCombMap.alpha e)
  | some e, some e', .boundary _ => ClassProducer.boundaryGapOf (outerDarts S.diagram) e e'
  | _, _, _ => []

theorem junctionGap_cell (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    {e e' : S.diagram.toCombMap.Dart} (he : (P.sideDarts k s).getLast? = some e)
    (he' : (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some e') {j : Fin S.diagram.rCellCount}
    (hj : P.kind k s = .cell j) :
    P.junctionGap k s = ClassProducer.cellGapOf S.diagram.toCombMap
      (S.diagram.toCombMap.alpha e') (S.diagram.toCombMap.alpha e) := by
  simp only [junctionGap, he, he', hj]

theorem junctionGap_boundary (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    {e e' : S.diagram.toCombMap.Dart} (he : (P.sideDarts k s).getLast? = some e)
    (he' : (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some e') {j : ℕ}
    (hj : P.kind k s = .boundary j) :
    P.junctionGap k s = ClassProducer.boundaryGapOf (outerDarts S.diagram) e e' := by
  simp only [junctionGap, he, he', hj]

open Classical in
/-- **Class-level join.**  Sides `s` and `s + 1` of polygon `k` join at kind level, the gap between
them reads a word of value one, a same-cell gap has no dart on the polygon face, and a same-section
junction moves forward along `∂Δ`. -/
def ClassJoins (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ) : Prop :=
  P.KindJoins k s ∧
    RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) = 1 ∧
    (∀ j, P.kind k s = .cell j →
      ∀ d ∈ P.junctionGap k s, S.diagram.toCombMap.faceOf d ≠ P.face k) ∧
    ∀ j, P.kind k s = .boundary j → ∀ e ∈ (P.sideDarts k s).getLast?,
      ∀ e' ∈ (P.sideDarts k ((s + 1) % P.sideCount k)).head?,
        (outerDarts S.diagram).idxOf e < (outerDarts S.diagram).idxOf e'

open Classical in
/-- The sides of polygon `k` that join the next side at kind level but not at class level. -/
noncomputable def badJunctions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (Finset.range (P.sideCount k)).filter fun s => P.KindJoins k s ∧ ¬ P.ClassJoins k s

end OsinLemma94RealizedPolygons

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ClassProducer.head?_cellGapOf
#audit_axioms GroupApproximation.GGT.VanKampen.ClassProducer.getLast?_cellGapOf
#audit_axioms GroupApproximation.GGT.VanKampen.ClassProducer.isChain_cellGapOf
#audit_axioms GroupApproximation.GGT.VanKampen.ClassProducer.isChain_append_cellGapOf
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.junctionGap_cell
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.junctionGap_boundary
