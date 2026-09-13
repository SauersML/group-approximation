import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollar
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSideFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# The stages of a collar insertion

The collar insertion (`GeodesicCollarStatement`) runs in three stages on a face set `S` whose
boundary darts form a simple closed walk `s ++ rest`.

1. **Strip** (`StripStatement`): pass to a diagram with a G-face of the face set enumerated by
   `s ++ q`, whose darts `q` cross into the face set (`Strip`).
2. **Insert** (`InsertStatement`): for a nonempty word `g` of the value of `s`, insert a path
   reading `g` through the strip, and cut the side `s` off the face set.
3. **Join** (`JoinStatement`): for a side of value one with a nonempty rest, join the two ends of
   the side across the strip, and cut the side off the face set.

Each stage is a transport of the diagram (`Transport`), and transports compose
(`Transport.trans`).  The last two stages end with a face set whose boundary darts are the darts
of a simple closed walk `collar ++ rest` (`WalkOutput`).  Such a walk enumerates a boundary cycle
of the face set, so the faces on its side are the face set (`sideFaces_boundaryCycle_eq`), and
the pocket region of the walk (`PocketRegion.ofSimpleClosedWalk`) gives the collar output
(`geodesicCollarOutput_of_walkOutput`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse SimpleClosedWalkSides

universe u w v

/-- A simple closed walk that enumerates the boundary darts of a face set is a boundary cycle of
the face set: the vertices of the walk are distinct, so its darts are. -/
def boundaryCycleOfSimpleClosedWalk {M : CombMap.{v}} {faces : Finset M.Face}
    {walk : List M.Dart} (hw : IsSimpleClosedWalk M walk)
    (hboundary : ∀ d, IsBoundaryDart M faces d ↔ d ∈ walk) : BoundaryCycle M faces where
  cycle := walk
  cycle_nonempty := hw.ne_nil
  cycle_nodup := List.Nodup.of_map M.vertexOf hw.vertex_nodup
  cycle_mem_iff d := (hboundary d).symm

namespace GeodesicCollar

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A transport of the collar surgery** from a face set `S` of `Δ` to a face set `S'` of `Δ'`:
an O-equivalence, an embedding of the darts compatible with `alpha` and the labels, labels in the
letters of `D`, the outer boundary and the relator cells outside `S` keeping their darts, and every
relator cell staying on its side of the face set. -/
structure Transport (D : RelGenSet G Lambda) {Delta : DiscDiagram.{u, w, v} W}
    (S : Finset Delta.toCombMap.Face) (Delta' : DiscDiagram.{u, w, v} W)
    (S' : Finset Delta'.toCombMap.Face) where
  equiv : OEquivalentDiscDiagram Delta Delta'
  embedding : Delta.toCombMap.Dart ↪ Delta'.toCombMap.Dart
  label_isLetter : ∀ d, D.IsLetter (Delta'.label d)
  alpha_embedding : ∀ d,
    Delta'.toCombMap.alpha (embedding d) = embedding (Delta.toCombMap.alpha d)
  label_embedding : ∀ d, Delta'.label (embedding d) = Delta.label d
  outerDarts_eq : Embedded.outerDarts Delta' = (Embedded.outerDarts Delta).map embedding
  cellDarts_eq : ∀ i : Fin Delta.rCellCount, (Embedded.cell Delta i).face ∉ S →
    Embedded.cellDarts Delta' (equiv.cellIndex i) = (Embedded.cellDarts Delta i).map embedding
  cell_mem_iff : ∀ i : Fin Delta.rCellCount,
    (Embedded.cell Delta' (equiv.cellIndex i)).face ∈ S' ↔ (Embedded.cell Delta i).face ∈ S

/-- The identity transport. -/
def Transport.refl (D : RelGenSet G Lambda) {Delta : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) (S : Finset Delta.toCombMap.Face) :
    Transport D S Delta S where
  equiv := OEquivalentDiscDiagram.refl Delta
  embedding := Function.Embedding.refl _
  label_isLetter := hlabel
  alpha_embedding _ := rfl
  label_embedding _ := rfl
  outerDarts_eq := (List.map_id _).symm
  cellDarts_eq _ _ := (List.map_id _).symm
  cell_mem_iff _ := Iff.rfl

/-- Transports compose. -/
def Transport.trans {D : RelGenSet G Lambda} {Delta₁ Delta₂ Delta₃ : DiscDiagram.{u, w, v} W}
    {S₁ : Finset Delta₁.toCombMap.Face} {S₂ : Finset Delta₂.toCombMap.Face}
    {S₃ : Finset Delta₃.toCombMap.Face} (T₁ : Transport D S₁ Delta₂ S₂)
    (T₂ : Transport D S₂ Delta₃ S₃) : Transport D S₁ Delta₃ S₃ where
  equiv :=
    { boundaryWord_eq := T₂.equiv.boundaryWord_eq.trans T₁.equiv.boundaryWord_eq
      cellIndex := T₁.equiv.cellIndex.trans T₂.equiv.cellIndex
      cellWord_eq := fun i =>
        (T₂.equiv.cellWord_eq (T₁.equiv.cellIndex i)).trans (T₁.equiv.cellWord_eq i) }
  embedding := T₁.embedding.trans T₂.embedding
  label_isLetter := T₂.label_isLetter
  alpha_embedding d :=
    (T₂.alpha_embedding (T₁.embedding d)).trans (congrArg T₂.embedding (T₁.alpha_embedding d))
  label_embedding d := (T₂.label_embedding (T₁.embedding d)).trans (T₁.label_embedding d)
  outerDarts_eq := by
    rw [T₂.outerDarts_eq, T₁.outerDarts_eq, List.map_map]
    rfl
  cellDarts_eq i hi := by
    have hi₂ : (Embedded.cell Delta₂ (T₁.equiv.cellIndex i)).face ∉ S₂ :=
      fun h => hi ((T₁.cell_mem_iff i).mp h)
    refine (T₂.cellDarts_eq (T₁.equiv.cellIndex i) hi₂).trans ?_
    rw [T₁.cellDarts_eq i hi, List.map_map]
    rfl
  cell_mem_iff i := (T₂.cell_mem_iff (T₁.equiv.cellIndex i)).trans (T₁.cell_mem_iff i)

/-- **A strip along a side** `p` of a face set `S`, where `p ++ r` is the boundary walk of `S`: a
G-face enumerated by `p ++ q`, whose darts `q` cross into `S`.  The face set avoids the exterior. -/
structure Strip (Delta : DiscDiagram.{u, w, v} W) (S : Finset Delta.toCombMap.Face)
    (p r : List Delta.toCombMap.Dart) where
  q : List Delta.toCombMap.Dart
  p_ne_nil : p ≠ []
  q_ne_nil : q ≠ []
  cycle : Delta.toCombMap.IsFaceCycle (p ++ q)
  not_cell : ∀ C ∈ Delta.relatorCells, C.face ≠ Delta.toCombMap.faceOf (p.head p_ne_nil)
  alpha_mem : ∀ e ∈ q, Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) ∈ S
  walk : IsSimpleClosedWalk Delta.toCombMap (p ++ r)
  boundary : ∀ d, IsBoundaryDart Delta.toCombMap S d ↔ d ∈ p ++ r
  outerFace_not_mem : Delta.outerFace ∉ S

namespace Strip

variable {Delta : DiscDiagram.{u, w, v} W} {S : Finset Delta.toCombMap.Face}
  {p r : List Delta.toCombMap.Dart} (X : Strip Delta S p r)

/-- The strip face is in the face set. -/
theorem face_mem : Delta.toCombMap.faceOf (p.head X.p_ne_nil) ∈ S :=
  ((X.boundary _).mpr (List.mem_append_left r (List.head_mem X.p_ne_nil))).1

/-- The strip face is not the exterior. -/
theorem face_ne_outer : Delta.toCombMap.faceOf (p.head X.p_ne_nil) ≠ Delta.outerFace :=
  fun h => X.outerFace_not_mem (by rw [← h]; exact X.face_mem)

end Strip

/-- **A collar walk** for a face set `S`, a list `r` of darts and a word `g`: a transport to a face
set `S'` avoiding the exterior, whose boundary darts are the darts of a simple closed walk
`collar ++ r.map ι` with `collar` reading `g`. -/
def WalkOutput (D : RelGenSet G Lambda) {Delta : DiscDiagram.{u, w, v} W}
    (S : Finset Delta.toCombMap.Face) (r : List Delta.toCombMap.Dart)
    (g : List (RelLetter G Lambda)) : Prop :=
  ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
    (T : Transport D S Delta' S') (collar : List Delta'.toCombMap.Dart),
    Delta'.outerFace ∉ S' ∧
    IsSimpleClosedWalk Delta'.toCombMap (collar ++ r.map T.embedding) ∧
    (∀ d, IsBoundaryDart Delta'.toCombMap S' d ↔ d ∈ collar ++ r.map T.embedding) ∧
    Embedded.dartWord Delta' collar = g

/-- A collar walk after a transport is a collar walk before it. -/
theorem WalkOutput.of_transport {D : RelGenSet G Lambda} {Delta₁ Delta₂ : DiscDiagram.{u, w, v} W}
    {S₁ : Finset Delta₁.toCombMap.Face} {S₂ : Finset Delta₂.toCombMap.Face}
    (T : Transport D S₁ Delta₂ S₂) {r : List Delta₁.toCombMap.Dart}
    {g : List (RelLetter G Lambda)} (h : WalkOutput D S₂ (r.map T.embedding) g) :
    WalkOutput D S₁ r g := by
  obtain ⟨Delta', S', T', collar, hout, hw, hboundary, hword⟩ := h
  have hmap : (r.map T.embedding).map T'.embedding = r.map (T.trans T').embedding := by
    rw [List.map_map]
    rfl
  refine ⟨Delta', S', T.trans T', collar, hout, ?_, ?_, hword⟩
  · rw [← hmap]
    exact hw
  · rw [← hmap]
    exact hboundary

/-- **The collar output from a collar walk** of the face set of a pocket region. -/
theorem geodesicCollarOutput_of_walkOutput (D : RelGenSet G Lambda)
    {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {rest : List Delta.toCombMap.Dart}
    {g : List (RelLetter G Lambda)} (h : WalkOutput D P.faces rest g) :
    GeodesicCollarOutput D P rest g := by
  obtain ⟨Delta'', faces, T, collar, houterFace, hw, hboundary, hword⟩ := h
  have hside : sideFaces Delta''.toCombMap (collar ++ rest.map T.embedding) = faces :=
    sideFaces_boundaryCycle_eq Delta''.planar.1 (boundaryCycleOfSimpleClosedWalk hw hboundary)
      houterFace
  have hout : Delta''.outerFace ∉ sideFaces Delta''.toCombMap (collar ++ rest.map T.embedding) := by
    rw [hside]
    exact houterFace
  obtain ⟨hin, hout'⟩ := PocketRegion.ofSimpleClosedWalk_followsBoundary hw hout
  refine ⟨Delta'', T.equiv, PocketRegion.ofSimpleClosedWalk hw hout, collar, T.embedding,
    T.label_isLetter, hin, hout', PocketRegion.ofSimpleClosedWalk_invDarts_outer hw hout, hword,
    T.alpha_embedding, T.label_embedding, T.outerDarts_eq,
    fun i hi => T.cellDarts_eq i ((P.mem_outside_iff _).mp hi), fun i => ?_⟩
  rw [PocketRegion.ofSimpleClosedWalk_faces, hside]
  exact T.cell_mem_iff i

/-- **Stage 1, the strip.**  A face set avoiding the exterior, whose boundary darts form a simple
closed walk `s ++ rest` with `s` nonempty, has a transport to a strip along the image of `s`. -/
def StripStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (S : Finset Delta.toCombMap.Face) (s rest : List Delta.toCombMap.Dart), s ≠ [] →
      IsSimpleClosedWalk Delta.toCombMap (s ++ rest) →
      (∀ d, IsBoundaryDart Delta.toCombMap S d ↔ d ∈ s ++ rest) → Delta.outerFace ∉ S →
      ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
        (T : Transport D S Delta' S'),
        Nonempty (Strip Delta' S' (s.map T.embedding) (rest.map T.embedding))

/-- **Stage 2, the insertion.**  A nonempty word in the letters of `D` with the value of the side
of a strip gives a collar walk reading the word. -/
def InsertStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (S : Finset Delta.toCombMap.Face) (p r : List Delta.toCombMap.Dart), Strip Delta S p r →
    ∀ (g : List (RelLetter G Lambda)), g ≠ [] → (∀ letter ∈ g, D.IsLetter letter) →
      RelLetter.listVal g = RelLetter.listVal (Embedded.dartWord Delta p) → WalkOutput D S r g

/-- **Stage 3, the join.**  A strip whose side has value one, with a nonempty rest, gives a collar
walk reading the empty word. -/
def JoinStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W),
    (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (S : Finset Delta.toCombMap.Face) (p r : List Delta.toCombMap.Dart), Strip Delta S p r →
      r ≠ [] → RelLetter.listVal (Embedded.dartWord Delta p) = 1 → WalkOutput D S r []

end GeodesicCollar

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.boundaryCycleOfSimpleClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Transport.trans
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.face_ne_outer
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.WalkOutput.of_transport
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.geodesicCollarOutput_of_walkOutput
