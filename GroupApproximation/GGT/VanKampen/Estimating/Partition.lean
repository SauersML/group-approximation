import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Positioned boundary partitions for embedded contiguity systems

This file constructs the cell-boundary partition from Appendix Definition M.
Every dart of a relator-cell boundary is indexed by its cyclic `Fin` position.
A bound dart points to an actual selected embedded region and remembers whether
the cell is its source or target.  A dart which occurs on no selected region is
unbound.  The classifier is defined by finite classical choice, so it exists
for every selected family and the exterior/interior/unbound perimeter identity
is automatic.

The final theorem isolates the numerical conversion used after Lemma 62: the
strict `n * sqrt rho` bound on unbound darts becomes the `2 * mu` uncovered
budget once every relator perimeter is at least `rho` and
`2 * mu * sqrt rho >= 1`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

namespace Embedded

/-- Classification of one positioned dart on a relator-cell boundary. -/
inductive CellArcKind
  | exterior
  | interior
  | unbound
  deriving DecidableEq

/-- An occurrence of a selected embedded region on the boundary of the
`i`-th relator cell. -/
inductive CellIncidence
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) : Type (max u w v)
  | source (candidate : Candidate D eps Delta)
      (mem_selected : candidate ∈ selected)
      (source_eq : candidate.contiguity.source = i)
  | target (candidate : Candidate D eps Delta)
      (mem_selected : candidate ∈ selected)
      (target_eq : candidate.contiguity.target = some i)

namespace CellIncidence

/-- A finite code distinguishing the source and target occurrence of a
selected candidate. -/
def code
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : Candidate D eps Delta × Bool :=
  match incidence with
  | .source candidate _ _ => (candidate, false)
  | .target candidate _ _ => (candidate, true)

/-- The candidate and source/target tag determine an incidence. -/
theorem code_injective
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount} :
    Function.Injective (code : CellIncidence selected i →
      Candidate D eps Delta × Bool) := by
  intro first second heq
  cases first <;> cases second <;> simp_all [code]

noncomputable instance incidenceFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount} : Fintype (CellIncidence selected i) := by
  classical
  exact Fintype.ofInjective code code_injective

/-- The cyclic cell arc carried by an incidence. -/
noncomputable def arc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : CyclicArc (cellDarts Delta i) := by
  cases incidence with
  | source candidate _ source_eq =>
      rw [← source_eq]
      exact candidate.contiguity.sourceArc
  | target candidate _ target_eq =>
      have hcarrier : targetDarts Delta candidate.contiguity.target =
          cellDarts Delta i := by
        rw [target_eq]
        rfl
      rw [← hcarrier]
      exact candidate.contiguity.targetArc

/-- A source occurrence aimed at the outer boundary is exterior; both
occurrences of a cell-to-cell region are interior. -/
noncomputable def kind
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : CellArcKind :=
  match incidence with
  | .source candidate _ _ =>
      if candidate.contiguity.target = none then
        CellArcKind.exterior
      else
        CellArcKind.interior
  | .target _ _ _ => CellArcKind.interior

/-- Positions of the fixed cell boundary occupied by one selected
incidence. -/
noncomputable def Position
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) :=
  {position : Fin (cellDarts Delta i).length //
    (cellDarts Delta i).get position ∈ incidence.arc.darts}

noncomputable instance positionFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : Fintype incidence.Position := by
  classical
  exact Fintype.ofInjective (fun position : incidence.Position => position.1)
    Subtype.val_injective

/-- The arc of an incidence has no repeated darts. -/
theorem arc_darts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : incidence.arc.darts.Nodup :=
  incidence.arc.darts_nodup (cellDarts_nodup Delta i)

/-- Occupied boundary positions are equivalent to the darts of the stored
cyclic arc. -/
noncomputable def positionEquivArcDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) :
    incidence.Position ≃
      {d : Delta.toCombMap.Dart // d ∈ incidence.arc.darts} := by
  classical
  let carrierEquiv : Fin (cellDarts Delta i).length ≃
      {d : Delta.toCombMap.Dart // d ∈ cellDarts Delta i} :=
    (cellDarts_nodup Delta i).getEquiv (cellDarts Delta i)
  let restricted : incidence.Position ≃
      {d : {d : Delta.toCombMap.Dart // d ∈ cellDarts Delta i} //
        d.1 ∈ incidence.arc.darts} :=
    carrierEquiv.subtypeEquiv fun _ => Iff.rfl
  let forgetCarrier :
      {d : {d : Delta.toCombMap.Dart // d ∈ cellDarts Delta i} //
          d.1 ∈ incidence.arc.darts} ≃
        {d : Delta.toCombMap.Dart // d ∈ incidence.arc.darts} :=
    { toFun := fun d => ⟨d.1.1, d.2⟩
      invFun := fun d =>
        ⟨⟨d.1, incidence.arc.mem_cycle_of_mem_darts d.2⟩, d.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact restricted.trans forgetCarrier

/-- The number of occupied positions of an incidence is exactly its stored
arc length. -/
theorem card_position
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) :
    Fintype.card incidence.Position = incidence.arc.length := by
  classical
  calc
    Fintype.card incidence.Position =
        Fintype.card {d : Delta.toCombMap.Dart // d ∈ incidence.arc.darts} :=
      Fintype.card_congr incidence.positionEquivArcDarts
    _ = Fintype.card (Fin incidence.arc.darts.length) := by
      exact Fintype.card_congr
        ((incidence.arc_darts_nodup.getEquiv incidence.arc.darts).symm)
    _ = incidence.arc.length := by
      rw [Fintype.card_fin, incidence.arc.darts_length]

/-- Incidences of one of the three boundary kinds at a fixed cell. -/
def OfKind
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (kind : CellArcKind) :=
  {incidence : CellIncidence selected i // incidence.kind = kind}

noncomputable instance ofKindFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount} {kind : CellArcKind} :
    Fintype (OfKind (selected := selected) (i := i) kind) := by
  classical
  exact Fintype.ofInjective
    (fun incidence : OfKind (selected := selected) (i := i) kind => incidence.1)
    Subtype.val_injective

/-- An occurrence is an incidence of the chosen kind together with one of
the cell positions occupied by its arc. -/
noncomputable def Occurrence
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (kind : CellArcKind) :=
  Σ incidence : OfKind (selected := selected) (i := i) kind,
    incidence.1.Position

noncomputable instance occurrenceFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount} {kind : CellArcKind} :
    Fintype (Occurrence (selected := selected) (i := i) kind) := by
  unfold Occurrence
  infer_instance

/-- Counting occurrences fibrewise sums the stored lengths of all incidences
of the chosen kind. -/
theorem card_occurrence_eq_sum_arcLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (kind : CellArcKind) :
    Fintype.card (Occurrence (selected := selected) (i := i) kind) =
      ∑ incidence : OfKind (selected := selected) (i := i) kind,
        incidence.1.arc.length := by
  classical
  change Fintype.card
      (Σ incidence : OfKind (selected := selected) (i := i) kind,
        incidence.1.Position) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro incidence _
  exact incidence.1.card_position

end CellIncidence

/-- No positioned cell dart belongs to two distinct selected incidences.  The
face-disjointness lemmas in `Embedded.lean` prove this once Lemma 65(a) has
excluded loop regions. -/
def IncidencePositionUnique
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) : Prop :=
  ∀ (i : Fin Delta.rCellCount)
    (position : Fin (cellDarts Delta i).length)
    (first second : CellIncidence selected i),
      (cellDarts Delta i).get position ∈ first.arc.darts →
      (cellDarts Delta i).get position ∈ second.arc.darts →
      first = second

/-- The empty selected family has unique incidence at every position. -/
theorem incidencePositionUnique_emptyModel
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W} :
    IncidencePositionUnique
      (∅ : Finset (Candidate D eps Delta)) := by
  intro i position first
  cases first with
  | source candidate mem_selected source_eq =>
      simp at mem_selected
  | target candidate mem_selected target_eq =>
      simp at mem_selected

/-- The singleton cyclic arc at one actual dart position. -/
def singletonArc
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount}
    (position : Fin (cellDarts Delta i).length) :
    CyclicArc (cellDarts Delta i) where
  start := ⟨position.1, lt_trans position.2 (Nat.lt_succ_self _)⟩
  length := 1
  length_le := Nat.one_le_iff_ne_zero.mpr fun hzero => by
    rw [hzero] at position
    exact Fin.elim0 position

/-- Classification of the dart at one cyclic position.  A bound classifier
includes the selected incidence whose stored cyclic arc contains that dart. -/
inductive CellDartClass
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount)
    (position : Fin (cellDarts Delta i).length) : Type (max u w v)
  | bound (incidence : CellIncidence selected i)
      (dart_mem : (cellDarts Delta i).get position ∈ incidence.arc.darts)
  | unbound

namespace CellDartClass

/-- The cyclic base position of a classified singleton dart. -/
def arc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    {position : Fin (cellDarts Delta i).length}
    (_classification : CellDartClass selected i position) :
    CyclicArc (cellDarts Delta i) := singletonArc position

/-- Kind of a classified positioned dart. -/
noncomputable def kind
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    {position : Fin (cellDarts Delta i).length}
    (classification : CellDartClass selected i position) : CellArcKind :=
  match classification with
  | .bound incidence _ => incidence.kind
  | .unbound => CellArcKind.unbound

end CellDartClass

/-- A complete cyclic classification of one relator-cell boundary. -/
structure CellBoundaryPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) where
  classify : ∀ position : Fin (cellDarts Delta i).length,
    CellDartClass selected i position

namespace CellBoundaryPartition

/-- Classify a dart as bound exactly when some selected incidence contains it.
The candidate and side are chosen from a finite type, but no ordering choice
affects any of the three resulting length totals. -/
noncomputable def canonical
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) : CellBoundaryPartition selected i where
  classify := fun position => by
    by_cases hbound : ∃ incidence : CellIncidence selected i,
        (cellDarts Delta i).get position ∈ incidence.arc.darts
    · exact CellDartClass.bound (Classical.choose hbound)
        (Classical.choose_spec hbound)
    · exact CellDartClass.unbound

/-- Under incidence uniqueness, the canonical classifier has the kind of any
incidence occupying the position. -/
theorem canonical_kind_of_mem
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (hunique : IncidencePositionUnique selected)
    (i : Fin Delta.rCellCount)
    (position : Fin (cellDarts Delta i).length)
    (incidence : CellIncidence selected i)
    (hmem : (cellDarts Delta i).get position ∈ incidence.arc.darts) :
    ((canonical selected i).classify position).kind = incidence.kind := by
  unfold canonical
  dsimp only
  split
  next hbound =>
    have heq : Classical.choose hbound = incidence :=
      hunique i position (Classical.choose hbound) incidence
        (Classical.choose_spec hbound) hmem
    cases heq
    rfl
  next hbound =>
    exact (hbound ⟨incidence, hmem⟩).elim

/-- Positions classified with one fixed kind. -/
def ClassifiedPosition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) (kind : CellArcKind) :=
  {position : Fin (cellDarts Delta i).length //
    (partition.classify position).kind = kind}

noncomputable instance classifiedPositionFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    {partition : CellBoundaryPartition selected i} {kind : CellArcKind} :
    Fintype (ClassifiedPosition partition kind) := by
  classical
  exact Fintype.ofInjective
    (fun position : ClassifiedPosition partition kind => position.1)
    Subtype.val_injective

/-- A canonical non-unbound position exposes the selected incidence which
occupies it. -/
theorem exists_incidence_of_canonical_kind
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) (kind : CellArcKind)
    (hkind : kind ≠ CellArcKind.unbound)
    (position : ClassifiedPosition (canonical selected i) kind) :
    ∃ incidence : CellIncidence selected i,
      incidence.kind = kind ∧
        (cellDarts Delta i).get position.1 ∈ incidence.arc.darts := by
  cases hclass : (canonical selected i).classify position.1 with
  | bound incidence hmem =>
      refine ⟨incidence, ?_, hmem⟩
      have hposition := position.2
      rw [hclass] at hposition
      exact hposition
  | unbound =>
      have hposition := position.2
      rw [hclass] at hposition
      exact (hkind hposition.symm).elim

/-- Under incidence uniqueness, occurrences of a non-unbound kind are
equivalent to the positions which the canonical partition gives that kind. -/
noncomputable def occurrenceEquivClassifiedPosition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (hunique : IncidencePositionUnique selected)
    (i : Fin Delta.rCellCount) (kind : CellArcKind)
    (hkind : kind ≠ CellArcKind.unbound) :
    CellIncidence.Occurrence (selected := selected) (i := i) kind ≃
      ClassifiedPosition (canonical selected i) kind := by
  let toClassified :
      CellIncidence.Occurrence (selected := selected) (i := i) kind →
        ClassifiedPosition (canonical selected i) kind :=
    fun occurrence =>
      ⟨occurrence.2.1, canonical_kind_of_mem selected hunique i occurrence.2.1
        occurrence.1.1 occurrence.2.2 |>.trans occurrence.1.2⟩
  apply Equiv.ofBijective toClassified
  constructor
  · intro first second heq
    have hposition : first.2.1 = second.2.1 :=
      congrArg Subtype.val heq
    have hsecondMem :
        (cellDarts Delta i).get first.2.1 ∈ second.1.1.arc.darts := by
      rw [hposition]
      exact second.2.2
    have hincidence : first.1.1 = second.1.1 :=
      hunique i first.2.1 first.1.1 second.1.1 first.2.2 hsecondMem
    cases first with
    | mk firstIncidence firstPosition =>
      cases second with
      | mk secondIncidence secondPosition =>
        dsimp only at hposition hincidence ⊢
        have hincidence' : firstIncidence = secondIncidence :=
          Subtype.ext hincidence
        subst secondIncidence
        have hposition' : firstPosition = secondPosition :=
          Subtype.ext hposition
        subst secondPosition
        rfl
  · intro position
    obtain ⟨incidence, hincidenceKind, hmem⟩ :=
      exists_incidence_of_canonical_kind selected i kind hkind position
    let occurrence :
        CellIncidence.Occurrence (selected := selected) (i := i) kind :=
      ⟨⟨incidence, hincidenceKind⟩, ⟨position.1, hmem⟩⟩
    refine ⟨occurrence, ?_⟩
    apply Subtype.ext
    rfl

/-- The canonical classifier makes every cell boundary partition inhabited. -/
theorem nonempty
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) :
    Nonempty (CellBoundaryPartition selected i) :=
  ⟨canonical selected i⟩

/-- Number of boundary darts of one kind. -/
noncomputable def kindLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) (kind : CellArcKind) : ℕ :=
  (Finset.univ.filter fun position => (partition.classify position).kind = kind).card

/-- The cardinality of the classified-position subtype is the corresponding
filtered length. -/
theorem card_classifiedPosition_eq_kindLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) (kind : CellArcKind) :
    Fintype.card (ClassifiedPosition partition kind) =
      partition.kindLength kind := by
  classical
  let classifiedFinset := Finset.univ.filter fun position =>
    (partition.classify position).kind = kind
  let positionEquiv : ClassifiedPosition partition kind ≃
      {position : Fin (cellDarts Delta i).length //
        position ∈ classifiedFinset} :=
    (Equiv.refl _).subtypeEquiv fun position => by
      simp only [ClassifiedPosition, classifiedFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
  calc
    Fintype.card (ClassifiedPosition partition kind) =
        Fintype.card {position : Fin (cellDarts Delta i).length //
          position ∈ classifiedFinset} :=
      Fintype.card_congr positionEquiv
    _ = classifiedFinset.card := Fintype.card_coe classifiedFinset
    _ = partition.kindLength kind := by rfl

/-- With unique positioned incidences, the canonical length of every
non-unbound kind is the sum of the stored cyclic arc lengths of its
incidences. -/
theorem canonical_kindLength_eq_sum_arcLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (hunique : IncidencePositionUnique selected)
    (i : Fin Delta.rCellCount) (kind : CellArcKind)
    (hkind : kind ≠ CellArcKind.unbound) :
    (canonical selected i).kindLength kind =
      ∑ incidence : CellIncidence.OfKind
          (selected := selected) (i := i) kind,
        incidence.1.arc.length := by
  calc
    (canonical selected i).kindLength kind =
        Fintype.card (ClassifiedPosition (canonical selected i) kind) :=
      (card_classifiedPosition_eq_kindLength (canonical selected i) kind).symm
    _ = Fintype.card
        (CellIncidence.Occurrence (selected := selected) (i := i) kind) :=
      (Fintype.card_congr
        (occurrenceEquivClassifiedPosition selected hunique i kind hkind)).symm
    _ = ∑ incidence : CellIncidence.OfKind
          (selected := selected) (i := i) kind,
        incidence.1.arc.length :=
      CellIncidence.card_occurrence_eq_sum_arcLength kind

/-- The three classifications partition the number of actual dart positions. -/
theorem cellDarts_length_eq_kindLengths
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) :
    (cellDarts Delta i).length =
      partition.kindLength CellArcKind.exterior +
      partition.kindLength CellArcKind.interior +
      partition.kindLength CellArcKind.unbound := by
  classical
  rw [← Fintype.card_fin (cellDarts Delta i).length]
  simp only [kindLength, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [show Fintype.card (Fin (cellDarts Delta i).length) =
      ∑ _position : Fin (cellDarts Delta i).length, 1 by simp]
  apply Finset.sum_congr rfl
  intro position _
  cases (partition.classify position).kind <;> simp

/-- The dart cycle of an indexed cell has the length of its relator word. -/
theorem cellDarts_length_eq_word_length
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    (cellDarts Delta i).length = (cell Delta i).word.length := by
  have hlength := congrArg List.length (dartWord_cellDarts Delta i)
  simpa only [dartWord, List.length_map] using hlength

/-- Exterior, interior, and unbound positioned darts partition the cell
perimeter exactly. -/
theorem perimeter_eq_kindLengths
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) :
    (cell Delta i).word.length =
      partition.kindLength CellArcKind.exterior +
      partition.kindLength CellArcKind.interior +
      partition.kindLength CellArcKind.unbound := by
  rw [← cellDarts_length_eq_word_length Delta i]
  exact partition.cellDarts_length_eq_kindLengths

end CellBoundaryPartition

/-- Canonical positioned boundary partitions for all relator cells of one
selected embedded family. -/
noncomputable def DiagramBoundaryPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :=
  ∀ i : Fin Delta.rCellCount, CellBoundaryPartition selected i

/-- The canonical diagram partition exists for every selected family. -/
noncomputable def canonicalDiagramPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    DiagramBoundaryPartition selected :=
  fun i => CellBoundaryPartition.canonical selected i

namespace DiagramBoundaryPartition

/-- Real weight of one class of positioned cell darts. -/
noncomputable def kindWeight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected)
    (kind : CellArcKind) (i : Fin Delta.rCellCount) : ℝ :=
  (partition i).kindLength kind

/-- The real-valued partition used by the contiguity count. -/
theorem cellWeight_partition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected)
    (i : Fin Delta.rCellCount) :
    ((Embedded.cell Delta i).word.length : ℝ) =
      partition.kindWeight CellArcKind.exterior i +
      partition.kindWeight CellArcKind.interior i +
      partition.kindWeight CellArcKind.unbound i := by
  simp only [kindWeight]
  exact_mod_cast (partition i).perimeter_eq_kindLengths

/-- Total number of unbound cell-boundary darts. -/
noncomputable def unboundTotal
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected) : ℕ :=
  ∑ i : Fin Delta.rCellCount,
    (partition i).kindLength CellArcKind.unbound

/-- Lemma 62's strict `n * sqrt rho` estimate implies the `2 * mu`
uncovered budget used by the final count. -/
theorem unbound_total_le_two_mu
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected)
    (mu : ℝ) (rho : ℕ)
    (hperimeter : ∀ i : Fin Delta.rCellCount,
      rho ≤ (Embedded.cell Delta i).word.length)
    (hlemma62 : (partition.unboundTotal : ℝ) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ))
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    (∑ i : Fin Delta.rCellCount,
        partition.kindWeight CellArcKind.unbound i) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ) := by
  have hrhoPos : 0 < (rho : ℝ) := by
    by_contra hrho
    have hrhoZero : (rho : ℝ) = 0 := le_antisymm (le_of_not_gt hrho) (by positivity)
    rw [hrhoZero, Real.sqrt_zero, mul_zero] at hthreshold
    norm_num at hthreshold
  have hsqrtPos : 0 < Real.sqrt (rho : ℝ) := Real.sqrt_pos.2 hrhoPos
  have hsqrtSq : Real.sqrt (rho : ℝ) * Real.sqrt (rho : ℝ) = (rho : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hrhoPos)
  have hperimeterSum :
      (Delta.rCellCount : ℝ) * (rho : ℝ) ≤
        ∑ i : Fin Delta.rCellCount, ((Embedded.cell Delta i).word.length : ℝ) := by
    calc
      (Delta.rCellCount : ℝ) * (rho : ℝ) =
          ∑ _i : Fin Delta.rCellCount, (rho : ℝ) := by simp
      _ ≤ ∑ i : Fin Delta.rCellCount, ((Embedded.cell Delta i).word.length : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast hperimeter i
  have hscale :
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) ≤
        2 * mu * ((Delta.rCellCount : ℝ) * (rho : ℝ)) := by
    have hn : 0 ≤ (Delta.rCellCount : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hthreshold
      (mul_nonneg hn (le_of_lt hsqrtPos))
    nlinarith
  have hbudget : (partition.unboundTotal : ℝ) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ) := by
    have hmuNonneg : 0 ≤ 2 * mu := by
      have : 0 ≤ mu := by nlinarith [hthreshold, hsqrtPos]
      positivity
    exact le_trans (le_of_lt hlemma62)
      (le_trans hscale (mul_le_mul_of_nonneg_left hperimeterSum hmuNonneg))
  have hunboundCast :
      (partition.unboundTotal : ℝ) =
        ∑ i : Fin Delta.rCellCount,
          partition.kindWeight CellArcKind.unbound i := by
    simp only [unboundTotal, kindWeight, Nat.cast_sum]
  rwa [hunboundCast] at hbudget

end DiagramBoundaryPartition

end Embedded

end VanKampen
end GGT
end GroupApproximation
