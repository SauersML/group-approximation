import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.Regions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionExclusion
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoinsCellArc
import GroupApproximation.Meta.AxiomGuard

/-!
# End loops of the class producer: cell classes as face walks

A class of kind `cell i` is the reverse of a face walk `seg y ℓ` of cell `i`.  Its first dart is
the reverse of the last dart of the walk and its last dart is `α y`.  When the polygon has a
single class, the class closes up: its value is one, and the walk turns around the vertex from
its last dart back to `y`, so the walk is a pocket of the cell.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

section Walks

variable {M : CombMap.{v}}

theorem head?_reverse_map_seg (x : M.Dart) (m : ℕ) :
    ((seg M x (m + 1)).reverse.map M.alpha).head? = some (M.alpha ((M.facePerm ^ m) x)) := by
  rw [List.head?_map, List.head?_reverse, seg_succ, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.map_some]

theorem getLast?_reverse_map_seg (x : M.Dart) (m : ℕ) :
    ((seg M x (m + 1)).reverse.map M.alpha).getLast? = some (M.alpha x) := by
  rw [List.getLast?_map, List.getLast?_reverse, seg_succ', List.head?_cons, Option.map_some]

theorem mem_of_alpha_mem_reverse_map {l : List M.Dart} {z : M.Dart}
    (h : M.alpha z ∈ l.reverse.map M.alpha) : z ∈ l := by
  obtain ⟨y, hy, hyz⟩ := List.mem_map.mp h
  rw [M.alpha.injective hyz] at hy
  exact List.mem_reverse.mp hy

theorem alpha_mem_reverse_map {l : List M.Dart} {z : M.Dart} (h : z ∈ l) :
    M.alpha z ∈ l.reverse.map M.alpha :=
  List.mem_map.mpr ⟨z, List.mem_reverse.mpr h, rfl⟩

end Walks

section Classes

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- The first dart of a class is the first dart of its first side. -/
theorem head?_classDarts (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i' : ℕ}
    (hi' : i' < Q.classCount k) :
    ∃ s0, (Q.classSides k i').head? = some s0 ∧ s0 < P.sideCount k ∧
      (Q.classDarts k i').head? = (P.sideDarts k s0).head? := by
  obtain ⟨s0, rest, hcons⟩ := List.exists_cons_of_ne_nil (Q.classSides_ne_nil k i' hi')
  have hlt : s0 < P.sideCount k :=
    Q.lt_sideCount_of_mem k i' hi' s0 (by rw [hcons]; exact List.mem_cons_self)
  refine ⟨s0, by rw [hcons, List.head?_cons], hlt, ?_⟩
  show ((Q.classSides k i').flatMap fun s => P.sideDarts k s ++ Q.gap k s).head? = _
  rw [hcons, List.flatMap_cons, List.head?_append, List.head?_append,
    List.head?_eq_some_head (P.side_ne_nil k s0 hlt), Option.some_or, Option.some_or]

/-- The last dart of a class is the last dart of its last side. -/
theorem getLast?_classDarts (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i' : ℕ}
    (hi' : i' < Q.classCount k) :
    ∃ sl, (Q.classSides k i').getLast? = some sl ∧ sl < P.sideCount k ∧
      (Q.classDarts k i').getLast? = (P.sideDarts k sl).getLast? := by
  obtain ⟨sl, hsl⟩ : ∃ sl, (Q.classSides k i').getLast? = some sl :=
    ⟨_, List.getLast?_eq_some_getLast (Q.classSides_ne_nil k i' hi')⟩
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hsl
  have hlt : sl < P.sideCount k := Q.lt_sideCount_of_mem k i' hi' sl (List.mem_of_getLast? hsl)
  have hgap : Q.gap k sl = [] := Q.gap_last k i' hi' sl (Option.mem_def.mpr hsl)
  refine ⟨sl, hsl, hlt, ?_⟩
  show ((Q.classSides k i').flatMap fun s => P.sideDarts k s ++ Q.gap k s).getLast? = _
  rw [hys, List.flatMap_append, List.flatMap_singleton, hgap, List.append_nil,
    List.getLast?_append, List.getLast?_eq_some_getLast (P.side_ne_nil k sl hlt), Option.some_or]

/-- A dart across a cell side lies in a class of kind `cell i`, which is the reverse of a face
walk of cell `i`. -/
theorem exists_class (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {s : ℕ}
    {j i : Fin S.diagram.rCellCount} {z : S.diagram.toCombMap.Dart} (hs : s < P.sideCount k)
    (hj : P.kind k s = .cell j) (hz : z ∈ cellDarts S.diagram i)
    (hzs : S.diagram.toCombMap.alpha z ∈ P.sideDarts k s) :
    ∃ i', i' < Q.classCount k ∧ Q.classKind k i' = .cell i ∧
      ∃ y ℓ, y ∈ cellDarts S.diagram i ∧ ℓ ≤ (cellDarts S.diagram i).length ∧
        Q.classDarts k i' = (seg S.diagram.toCombMap y ℓ).reverse.map S.diagram.toCombMap.alpha ∧
        S.diagram.toCombMap.alpha z ∈ Q.classDarts k i' := by
  have hji : j = i := by
    have h1 := P.alpha_mem_cellDarts_of_mem_sideDarts hs hj hzs
    rw [S.diagram.toCombMap.alpha_involutive z] at h1
    exact cell_face_injective S.diagram
      ((faceOf_of_mem_cellDarts h1).symm.trans (faceOf_of_mem_cellDarts hz))
  rw [hji] at hj
  have hmem : s ∈ (List.range (Q.classCount k)).flatMap (Q.classSides k) := by
    rw [Q.sides_eq k, List.mem_rotate, List.mem_range]
    exact hs
  obtain ⟨i', hi', hsi⟩ := List.mem_flatMap.mp hmem
  have hi'' : i' < Q.classCount k := List.mem_range.mp hi'
  have hkind : Q.classKind k i' = .cell i := (Q.kind_eq k i' hi'' s hsi).symm.trans hj
  obtain ⟨arc, harc⟩ := Q.cell_arc k i' i hi'' hkind
  obtain ⟨y, hy, hA⟩ := arc_seg (i := i) rfl arc
  have hcl : Q.classDarts k i' =
      (seg S.diagram.toCombMap y arc.length).reverse.map S.diagram.toCombMap.alpha := by
    show ((Q.classSides k i').flatMap fun s => P.sideDarts k s ++ Q.gap k s) = _
    rw [harc]
    show arc.darts.reverse.map S.diagram.toCombMap.alpha = _
    rw [hA]
  refine ⟨i', hi'', hkind, y, arc.length, hy, arc.length_le, hcl, ?_⟩
  show S.diagram.toCombMap.alpha z ∈
    ((Q.classSides k i').flatMap fun s => P.sideDarts k s ++ Q.gap k s)
  exact List.mem_flatMap.mpr ⟨s, hsi, List.mem_append.mpr (Or.inl hzs)⟩

/-- The only class of a single-class polygon has value one. -/
theorem single_value (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {y : S.diagram.toCombMap.Dart} {l : ℕ} (hcount : Q.classCount k = 1)
    (hcl : Q.classDarts k 0 =
      (seg S.diagram.toCombMap y l).reverse.map S.diagram.toCombMap.alpha) :
    RelLetter.listVal (dartWord S.diagram (seg S.diagram.toCombMap y l)) = 1 := by
  have hc := Q.corner_closed k
  have hstep := Q.corner_step k 0
  rw [Nat.zero_add] at hstep
  rw [hcount, hstep] at hc
  have hv : RelLetter.listVal (Q.word k 0) = 1 := mul_left_cancel (hc.trans (mul_one _).symm)
  rw [OsinLemma94ClassPolygons.word, hcl, listVal_dartWord_reverse_alpha] at hv
  exact inv_eq_one.mp hv

/-- The only class of a single-class polygon turns around the vertex at its ends. -/
theorem single_closed (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {y : S.diagram.toCombMap.Dart} {m : ℕ} (hcount : Q.classCount k = 1)
    (hcl : Q.classDarts k 0 =
      (seg S.diagram.toCombMap y (m + 1)).reverse.map S.diagram.toCombMap.alpha) :
    S.diagram.toCombMap.sigma.SameCycle y ((S.diagram.toCombMap.facePerm ^ (m + 1)) y) := by
  obtain ⟨s0, hs0, _, hhead⟩ := head?_classDarts Q (k := k) (i' := 0) (by omega)
  obtain ⟨sl, hsl, hltl, hlast⟩ := getLast?_classDarts Q (k := k) (i' := 0) (by omega)
  rw [hcl, head?_reverse_map_seg] at hhead
  rw [hcl, getLast?_reverse_map_seg] at hlast
  have hsides := Q.sides_eq k
  rw [hcount, List.range_one, List.flatMap_singleton] at hsides
  rw [hsides] at hs0 hsl
  have hmod := rotate_range_head_last (by omega) hs0 hsl
  have he' : S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ m) y) ∈
      (P.sideDarts k ((sl + 1) % P.sideCount k)).head? := by
    rw [hmod]
    exact Option.mem_def.mpr hhead.symm
  have hf := P.facePerm_getLast_eq_head_mod hltl (Option.mem_def.mpr hlast.symm) he'
  have hsy : S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ m) y) =
      S.diagram.toCombMap.sigma y := by
    rw [← hf]
    show S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha y)) = _
    rw [S.diagram.toCombMap.alpha_involutive y]
  rw [pow_succ_apply y m]
  show S.diagram.toCombMap.sigma.SameCycle y
    (S.diagram.toCombMap.sigma
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ m) y)))
  rw [hsy]
  exact (Equiv.Perm.SameCycle.refl _ _).apply_right.apply_right

/-- The walk of the only class of a single-class polygon is a pocket. -/
theorem single_pocket (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i : Fin S.diagram.rCellCount} {y : S.diagram.toCombMap.Dart} {m : ℕ}
    (hcount : Q.classCount k = 1) (hy : y ∈ cellDarts S.diagram i)
    (hm : m + 1 ≤ (cellDarts S.diagram i).length)
    (hcl : Q.classDarts k 0 =
      (seg S.diagram.toCombMap y (m + 1)).reverse.map S.diagram.toCombMap.alpha) :
    IsPocket S.diagram i y (m + 1) :=
  ⟨hy, hm, single_closed Q hcount hcl, single_value Q hcount hcl⟩

end Classes

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.head?_reverse_map_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.getLast?_reverse_map_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.mem_of_alpha_mem_reverse_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.alpha_mem_reverse_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.head?_classDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.getLast?_classDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.exists_class
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.single_value
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.single_closed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.single_pocket
