import GroupApproximation.GGT.HullSCRelativeGreendlingerSpelling
import GroupApproximation.GGT.VanKampen.Estimating.UnboundParameters
import GroupApproximation.Meta.AxiomGuard

/-!
# A conjugate involution obstructs the unbound-budget statement

One relator cell spells `a`, while the outer boundary spells a conjugate
involution `b != a`.  At epsilon zero, the connector words are empty.  A
nonempty source arc would therefore have to equal an outer arc in value,
which is impossible.  With only one cell there are no interior incidences.
Thus the unique relator dart is unbound on every O-equivalent diagram.
-/

namespace GroupApproximation.GGT.VanKampen.Estimating.UnboundConjugateCounterexample

open GroupApproximation.HullSC GroupApproximation.WordMetric Embedded
open GroupApproximation.Manuscript.NonMF.TorsionFree

abbrev G := Equiv.Perm (Fin 3)
def a : G := Equiv.swap 0 1
def t : G := Equiv.swap 1 2
def b : G := t * a * t⁻¹

def D : RelGenSet G Empty where
  base := Set.univ
  fam := Empty.elim
  symmetricGenerating := by
    rw [Set.univ_union]
    exact ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩

def relator : List (RelLetter G Empty) := [.base a]
def outer : List (RelLetter G Empty) := [.base b]
def W : Set (List (RelLetter G Empty)) := {relator}

theorem a_ne_one : a ≠ 1 := by decide
theorem b_ne_one : b ≠ 1 := by decide
theorem a_ne_b : a ≠ b := by decide

theorem singleton_quasiGeodesic (g : G) :
    IsLambdaCQuasiGeodesicWord D 1 1 [.base g] := by
  refine ⟨?_, ?_⟩
  · intro letter hletter
    simp only [List.mem_singleton] at hletter
    subst letter
    exact Set.mem_univ _
  · intro i j hij hj
    have hlen : j - i ≤ 1 := by simpa using (Nat.sub_le j i).trans hj
    have hlenReal : ((j - i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hlen
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (wordDist D.alphabet.carrier (OsinComponents.vertex 1 ([.base g] : List (RelLetter G Empty)) i)
        (OsinComponents.vertex 1 ([.base g] : List (RelLetter G Empty)) j))
    linarith

theorem condition : OsinCCondition D W 0 (1 / 2) 1 1 1 := by
  refine {
    admissible := ?_
    inv_mem := ?_
    rotate_mem := ?_
    long := ?_
    deep := ?_
    pieces_small := ?_
    quasiGeodesic := ?_
    publishedPiecesSmall := ?_ }
  · intro word hword
    rcases Set.mem_singleton_iff.mp hword with rfl
    exact (singleton_quasiGeodesic a).1
  · intro word hword
    rcases Set.mem_singleton_iff.mp hword with rfl
    change RelWord.revInv relator = relator
    simp [RelWord.revInv, RelWord.inv, relator, a]
  · intro word hword n
    rcases Set.mem_singleton_iff.mp hword with rfl
    simp [W, relator]
  · intro word hword
    rcases Set.mem_singleton_iff.mp hword with rfl
    exact le_rfl
  · intro word hword letter hletter lam
    exact Empty.elim lam
  · intro first word hpiece
    obtain ⟨hw, _, other, ho, hne, _⟩ := hpiece
    exact (hne ((Set.mem_singleton_iff.mp ho).trans
      (Set.mem_singleton_iff.mp hw).symm)).elim
  · intro word hword
    rcases Set.mem_singleton_iff.mp hword with rfl
    exact singleton_quasiGeodesic a
  · intro first second word hpiece
    obtain ⟨hw, _, other, ho, _, _, y, z, hy, _, _, hne⟩ := hpiece
    have hyOne : y = 1 :=
      (wordNorm_eq_zero_iff D.alphabet.symmetricGenerating y).mp (Nat.le_zero.mp hy)
    have hwords : other = word :=
      (Set.mem_singleton_iff.mp ho).trans (Set.mem_singleton_iff.mp hw).symm
    exact (hne (by rw [hwords, hyOne]; simp)).elim

def algebraicCell : Lemma44OrientedRelatorCell W where
  relator := relator
  relator_mem := rfl
  conjugator := t

def Z : RelativeReducedDiagram D W 1 where
  boundaryWord := [b]
  boundary := b
  boundary_ne_one := b_ne_one
  boundaryWord_isWord := ⟨by intro x hx; exact Or.inl (Set.mem_univ _), by simp⟩
  boundary_length_le := by decide
  area := 1
  area_pos := by decide
  cells := [algebraicCell]
  cells_length := rfl
  cell_values_prod := by simp [algebraicCell, Lemma44OrientedRelatorCell.value,
    relator, RelLetter.listVal, RelLetter.val, b]
  no_cancelling_pair := by
    intro pre between suf first second hsplit
    have hlen := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  cell_relator_ne_nil := by
    rintro ⟨i, hi⟩
    change i < 1 at hi
    have hi0 : i = 0 := by omega
    subst i
    simp [algebraicCell, relator]

theorem exterior_eq_nil (C : RelativeBoundaryContiguity D 0 [b] relator) :
    C.exterior = [] := by
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
  cases he : C.exterior with
  | nil => rfl
  | cons x xs =>
    have hlen := C.exterior_length_le_relator
    have hxs : xs = [] := List.length_eq_zero_iff.mp (by
      simp only [he, relator, List.length_cons, List.length_nil] at hlen
      omega)
    have hx : x = RelLetter.base a := by
      apply List.mem_singleton.mp
      change x ∈ relator
      rw [C.relator_decomposition, he]
      simp
    have hvalue := C.exterior_value
    simp only [he, hxs, hx, hl, hr, RelLetter.listVal, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, RelLetter.val, mul_one,
      one_mul] at hvalue
    rcases harc with harc | harc
    · exact (a_ne_one (hvalue.trans harc)).elim
    · exact (a_ne_b (hvalue.trans harc)).elim

theorem target_eq_none {Delta : DiscDiagram.{0, 0, 0} W}
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

theorem sourceArc_length_eq_zero {Delta : DiscDiagram.{0, 0, 0} W}
    (hcount : Delta.rCellCount = 1) (hboundary : Delta.boundaryWord = outer)
    {faces : Finset Delta.toCombMap.Face} (Gamma : Contiguity D 0 Delta faces) :
    Gamma.sourceArc.length = 0 := by
  have hword : (cell Delta Gamma.source).word = relator :=
    Set.mem_singleton_iff.mp (cell Delta Gamma.source).word_mem
  have hconverted := exists_relativeBoundaryContiguity_rotated Gamma
    (target_eq_none hcount Gamma) [b] (by rw [hboundary]; rfl)
  rw [hword] at hconverted
  have hrotate : relator.rotate Gamma.sourceArc.start.val = relator := by
    change [RelLetter.base a].rotate _ = ([RelLetter.base a] : List (RelLetter G Empty))
    exact List.rotate_singleton _ _
  rw [hrotate] at hconverted
  obtain ⟨C, hC⟩ := hconverted
  rw [exterior_eq_nil C, List.length_nil] at hC
  exact hC.symm

theorem no_contiguity {Delta : DiscDiagram.{0, 0, 0} W}
    (hcount : Delta.rCellCount = 1) (hboundary : Delta.boundaryWord = outer)
    {faces : Finset Delta.toCombMap.Face} (Gamma : Contiguity D 0 Delta faces) : False := by
  have ht := target_eq_none hcount Gamma
  let arc : CyclicArc (outerDarts Delta) :=
    cast (congrArg CyclicArc (congrArg (targetDarts Delta) ht)) Gamma.targetArc
  have htarget : targetBoundaryDarts Delta Gamma.target Gamma.targetArc = arc.darts :=
    targetBoundaryDarts_cast ht Gamma.targetArc
  have hsource := sourceArc_length_eq_zero hcount hboundary Gamma
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
  simp only [outer, List.rotate_singleton] at hsplit
  have hnil : dartWord Delta arc.darts = [] := by
    cases he : dartWord Delta arc.darts with
    | nil => rfl
    | cons x xs =>
      rw [he, List.cons_append] at hsplit
      obtain ⟨hx, htail⟩ := List.cons.inj hsplit
      have hxs := (List.append_eq_nil_iff.mp htail.symm).1
      rw [he, hxs, ← hx] at hval
      exact (b_ne_one (by simpa [RelLetter.listVal, RelLetter.val] using hval)).elim
  have hdarts : arc.darts = [] := List.map_eq_nil_iff.mp hnil
  apply Gamma.boundary.cycle_nonempty
  rw [Gamma.boundary_decomposition, htarget, hdarts, hr, hl,
    CyclicArc.reverseDarts, CyclicArc.darts, hsource]
  simp

theorem selected_eq_empty {Delta : DiscDiagram.{0, 0, 0} W}
    (hcount : Delta.rCellCount = 1) (hboundary : Delta.boundaryWord = outer)
    (scaffold : EstimatingScaffold D 0 Delta) : scaffold.selected.family = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro candidate _
  exact no_contiguity hcount hboundary candidate.contiguity

theorem unboundTotal_eq_one {Delta : DiscDiagram.{0, 0, 0} W}
    (hcount : Delta.rCellCount = 1) (hboundary : Delta.boundaryWord = outer)
    (scaffold : EstimatingScaffold D 0 Delta) : scaffold.partition.unboundTotal = 1 := by
  classical
  have hempty := selected_eq_empty hcount hboundary scaffold
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
  have hlength (i : Fin Delta.rCellCount) :
      (scaffold.partition i).kindLength CellArcKind.unbound = 1 := by
    simp only [CellBoundaryPartition.kindLength, hkind, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin, CellBoundaryPartition.cellDarts_length_eq_word_length]
    have hword := Set.mem_singleton_iff.mp (cell Delta i).word_mem
    rw [hword]
    rfl
  simp only [DiagramBoundaryPartition.unboundTotal, hlength, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, hcount]

/-- An O-equivalent output cannot satisfy the strict budget: its single
relator dart remains unbound, so the asserted inequality is `1 < 1`. -/
theorem not_estimatingUnboundOutputStatement :
    ¬ EstimatingUnboundOutputStatement.{0, 0, 0} := by
  intro h
  obtain ⟨realization⟩ := relativeDiscRealizationSpellingStatement D W 1 Z outer rfl
  have hcount : realization.diagram.rCellCount = 1 := by
    have hc := Fintype.card_congr realization.cellIndex
    change Fintype.card (Fin 1) = Fintype.card (Fin realization.diagram.rCellCount) at hc
    simpa only [Fintype.card_fin] using hc.symm
  obtain ⟨scaffold⟩ := exists_estimatingScaffold D 0 realization.diagram
  obtain ⟨graph⟩ := estimatingGraphData_emptyFamilyModel D 0 realization.diagram scaffold
    (selected_eq_empty hcount realization.outerWord_eq scaffold)
  obtain ⟨Delta, ⟨hequiv⟩, _, scaffold', _, ⟨budget⟩⟩ :=
    h D 0 1 (1 / 2) 1 1 (by norm_num) condition realization.diagram realization.reduced
      (by omega) scaffold graph (by rw [realization.outerWord_eq]; exact singleton_quasiGeodesic b)
  have hc : Delta.rCellCount = 1 := hequiv.rCellCount_eq.trans hcount
  have hb : Delta.boundaryWord = outer := hequiv.boundaryWord_eq.trans realization.outerWord_eq
  have hlt := budget.unbound_lt
  rw [unboundTotal_eq_one hc hb scaffold', hc] at hlt
  norm_num at hlt

end GroupApproximation.GGT.VanKampen.Estimating.UnboundConjugateCounterexample

#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundConjugateCounterexample.not_estimatingUnboundOutputStatement
