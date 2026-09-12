import GroupApproximation.GGT.HullSCRelativeExteriorArcConversion
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# A zero-connector obstruction for one-cell diagrams

If every nonempty relator prefix has value different from both the identity
and the singleton outer label, an epsilon-zero contiguity cannot exist.
The obstruction depends only on cell words and the outer boundary, so it
survives O-equivalence. This supplies reusable checks on unbound estimates.
-/

namespace GroupApproximation.GGT.VanKampen.ZeroConnectorObstruction

open GroupApproximation.HullSC Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {b : G}

/-- A nonempty prefix of a word in the family cannot spell either possible
value of a subarc of the singleton outer boundary. -/
def PrefixValuesAvoid (W : Set (List (RelLetter G Lambda))) (b : G) : Prop :=
  ∀ word ∈ W, ∀ first suffix, word = first ++ suffix → first ≠ [] →
    RelLetter.listVal first ≠ 1 ∧ RelLetter.listVal first ≠ b

theorem exterior_eq_nil (havoid : PrefixValuesAvoid W b)
    {word : List (RelLetter G Lambda)} (hword : word ∈ W)
    (C : RelativeBoundaryContiguity D 0 [b] word) : C.exterior = [] := by
  have hl : C.leftSide = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp C.leftSide_short)
  have hr : C.rightSide = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp C.rightSide_short)
  have harc : C.boundaryArc.prod = 1 ∨ C.boundaryArc.prod = b := by
    have hlen := C.boundaryArc_length_le_boundaryWord
    have hmem : ∀ x ∈ C.boundaryArc, x = b := by
      intro x hx
      apply List.mem_singleton.mp
      have hdecomp := C.boundary_decomposition
      simp only [List.rotate_singleton] at hdecomp
      rw [hdecomp]
      simp only [List.mem_append]
      exact Or.inl (Or.inr hx)
    cases he : C.boundaryArc with
    | nil => simp
    | cons x xs =>
      have hxs : xs = [] := List.length_eq_zero_iff.mp (by
        simp only [he, List.length_cons, List.length_nil] at hlen
        omega)
      have hx := hmem x (by rw [he]; exact List.mem_cons_self)
      simp [hxs, hx]
  by_contra hne
  have havoid' := havoid word hword C.exterior C.remainder C.relator_decomposition hne
  have hvalue := C.exterior_value
  simp only [hl, hr, RelLetter.listVal_nil, one_mul, mul_one] at hvalue
  rcases harc with harc | harc
  · exact havoid'.1 (hvalue.trans harc)
  · exact havoid'.2 (hvalue.trans harc)

theorem target_eq_none {Delta : DiscDiagram.{u, w, v} W}
    (hcount : Delta.rCellCount = 1) {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D 0 Delta faces) : Gamma.target = none := by
  cases ht : Gamma.target with
  | none => rfl
  | some j =>
    exfalso
    apply Gamma.target_ne_source j ht
    apply Fin.ext
    have hi := Gamma.source.isLt
    have hj := j.isLt
    omega

theorem sourceArc_length_eq_zero {Delta : DiscDiagram.{u, w, v} W}
    (hcount : Delta.rCellCount = 1) (hboundary : Delta.boundaryWord = [.base b])
    (hrotate : ∀ word ∈ W, ∀ n : ℕ, word.rotate n ∈ W)
    (havoid : PrefixValuesAvoid W b)
    {faces : Finset Delta.toCombMap.Face} (Gamma : Contiguity D 0 Delta faces) :
    Gamma.sourceArc.length = 0 := by
  obtain ⟨C, hC⟩ := exists_relativeBoundaryContiguity_rotated Gamma
    (target_eq_none hcount Gamma) [b] (by rw [hboundary]; rfl)
  have hword := hrotate (cell Delta Gamma.source).word (cell Delta Gamma.source).word_mem
    Gamma.sourceArc.start.val
  rw [exterior_eq_nil havoid hword C, List.length_nil] at hC
  exact hC.symm

theorem no_contiguity {Delta : DiscDiagram.{u, w, v} W}
    (hcount : Delta.rCellCount = 1) (hboundary : Delta.boundaryWord = [.base b])
    (hb : b ≠ 1) (hrotate : ∀ word ∈ W, ∀ n : ℕ, word.rotate n ∈ W)
    (havoid : PrefixValuesAvoid W b)
    {faces : Finset Delta.toCombMap.Face} (Gamma : Contiguity D 0 Delta faces) : False := by
  have ht := target_eq_none hcount Gamma
  let arc : CyclicArc (outerDarts Delta) :=
    cast (congrArg CyclicArc (congrArg (targetDarts Delta) ht)) Gamma.targetArc
  have htarget : targetBoundaryDarts Delta Gamma.target Gamma.targetArc = arc.darts :=
    targetBoundaryDarts_cast ht Gamma.targetArc
  have hsource := sourceArc_length_eq_zero hcount hboundary hrotate havoid Gamma
  have hr : Gamma.rightSide = [] := List.length_eq_zero_iff.mp
    (Nat.le_zero.mp Gamma.rightSide_length_le)
  have hl : Gamma.leftSide = [] := List.length_eq_zero_iff.mp
    (Nat.le_zero.mp Gamma.leftSide_length_le)
  obtain ⟨l, shelling⟩ := Gamma.pasting
  have hvalue := Gamma.arcs_value_of_pasting (faceSetWordHomotopy_of_shelling shelling)
  simp only [htarget, hr, hl, CyclicArc.darts, hsource, List.take_zero,
    dartWord, List.map_nil, RelLetter.listVal_nil, one_mul, mul_one] at hvalue
  have hval : RelLetter.listVal (dartWord Delta arc.darts) = 1 := hvalue.symm
  obtain ⟨suffix, hsplit⟩ := arc.exists_dartWord_suffix
  rw [arc.dartWord_rotated, dartWord_outerDarts, hboundary] at hsplit
  simp only [List.rotate_singleton] at hsplit
  have hnil : dartWord Delta arc.darts = [] := by
    cases he : dartWord Delta arc.darts with
    | nil => rfl
    | cons x xs =>
      rw [he, List.cons_append] at hsplit
      obtain ⟨hx, htail⟩ := List.cons.inj hsplit
      have hxs := (List.append_eq_nil_iff.mp htail.symm).1
      rw [he, hxs, ← hx] at hval
      exact (hb (by simpa [RelLetter.listVal, RelLetter.val] using hval)).elim
  have hdarts : arc.darts = [] := List.map_eq_nil_iff.mp hnil
  apply Gamma.boundary.cycle_nonempty
  rw [Gamma.boundary_decomposition, htarget, hdarts, hr, hl,
    CyclicArc.reverseDarts, CyclicArc.darts, hsource]
  simp

theorem selected_eq_empty {Delta : DiscDiagram.{u, w, v} W}
    (hno : ∀ {faces : Finset Delta.toCombMap.Face}, Contiguity D 0 Delta faces → False)
    (scaffold : EstimatingScaffold D 0 Delta) : scaffold.selected.family = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro candidate _
  exact hno candidate.contiguity

theorem unboundTotal_eq_cellLength {Delta : DiscDiagram.{u, w, v} W}
    (hcount : Delta.rCellCount = 1) {n : ℕ}
    (hlength : ∀ i : Fin Delta.rCellCount, (cell Delta i).word.length = n)
    (hno : ∀ {faces : Finset Delta.toCombMap.Face}, Contiguity D 0 Delta faces → False)
    (scaffold : EstimatingScaffold D 0 Delta) : scaffold.partition.unboundTotal = n := by
  classical
  have hempty := selected_eq_empty hno scaffold
  have hinc (i : Fin Delta.rCellCount) (incidence : CellIncidence scaffold.selected.family i) :
      False := by
    cases incidence with
    | source candidate hmem _ => simp [hempty] at hmem
    | target candidate hmem _ => simp [hempty] at hmem
  have hkind (i : Fin Delta.rCellCount) (position : Fin (cellDarts Delta i).length) :
      ((scaffold.partition i).classify position).kind = CellArcKind.unbound := by
    cases (scaffold.partition i).classify position with
    | bound incidence _ => exact (hinc i incidence).elim
    | unbound => rfl
  have hcell (i : Fin Delta.rCellCount) :
      (scaffold.partition i).kindLength CellArcKind.unbound = n := by
    simp only [CellBoundaryPartition.kindLength, hkind, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin, CellBoundaryPartition.cellDarts_length_eq_word_length,
      hlength]
  simp only [DiagramBoundaryPartition.unboundTotal, hcell, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, hcount, one_mul]

end GroupApproximation.GGT.VanKampen.ZeroConnectorObstruction

#audit_axioms GroupApproximation.GGT.VanKampen.ZeroConnectorObstruction.no_contiguity
#audit_axioms GroupApproximation.GGT.VanKampen.ZeroConnectorObstruction.unboundTotal_eq_cellLength
