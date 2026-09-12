import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport actual face-set boundaries away from an insertion face

The embedding retains every old dart and every untouched ordered face cycle.
Consequently it preserves boundary incidence, the internal tracing moves and
shellings of any selected region avoiding the insertion face. These are
geometric transport lemmas; actual insertion constructs the embedding.
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded
universe u w v v'
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure DiscEmbeddingAway (Delta : DiscDiagram.{u, w, v} W)
    (Xi : DiscDiagram.{u, w, v'} W) (f : Delta.toCombMap.Face) where
  darts : Delta.toCombMap.Dart ↪ Xi.toCombMap.Dart
  faces : Delta.toCombMap.Face ↪ Xi.toCombMap.Face
  alpha : ∀ d, Xi.toCombMap.alpha (darts d) = darts (Delta.toCombMap.alpha d)
  label : ∀ d, Xi.label (darts d) = Delta.label d
  outer : Xi.outerFace = faces Delta.outerFace
  face_boundary : ∀ g, g ≠ f →
    (Xi.faceBoundary (faces g)).darts = (Delta.faceBoundary g).darts.map darts
  facePerm : ∀ d, Delta.toCombMap.faceOf d ≠ f →
    Xi.toCombMap.facePerm (darts d) = darts (Delta.toCombMap.facePerm d)

namespace DiscEmbeddingAway

variable {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {f : Delta.toCombMap.Face} (E : DiscEmbeddingAway Delta Xi f)

def faceSet (s : Finset Delta.toCombMap.Face) : Finset Xi.toCombMap.Face := s.map E.faces

theorem faceSet_card (s : Finset Delta.toCombMap.Face) : (E.faceSet s).card = s.card :=
  Finset.card_map E.faces

theorem faceSet_disjoint_iff (s t : Finset Delta.toCombMap.Face) :
    Disjoint (E.faceSet s) (E.faceSet t) ↔ Disjoint s t := by
  simp only [faceSet, Finset.disjoint_left, Finset.mem_map]
  constructor
  · intro h g hs ht
    exact h ⟨g, hs, rfl⟩ ⟨g, ht, rfl⟩
  · intro h x hx hy
    obtain ⟨g, hg, hgx⟩ := hx
    obtain ⟨j, hj, hjx⟩ := hy
    exact h hg (E.faces.injective (hjx.trans hgx.symm) ▸ hj)

theorem dartWord_map (l : List Delta.toCombMap.Dart) :
    dartWord Xi (l.map E.darts) = dartWord Delta l := by
  simp only [dartWord, List.map_map]
  exact List.map_congr_left (fun d _ => E.label d)

theorem faceWord_eq (g : Delta.toCombMap.Face) (hg : g ≠ f) :
    Xi.faceWord (E.faces g) = Delta.faceWord g := by
  change ((Xi.faceBoundary (E.faces g)).darts.map Xi.label) = _
  rw [E.face_boundary g hg]
  exact E.dartWord_map _

theorem faceOf_mem_iff (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (x : Xi.toCombMap.Dart) :
    Xi.toCombMap.faceOf x ∈ E.faceSet s ↔
      ∃ d : Delta.toCombMap.Dart, E.darts d = x ∧ Delta.toCombMap.faceOf d ∈ s := by
  constructor
  · intro hx
    obtain ⟨g, hg, hgx⟩ := Finset.mem_map.mp hx
    have hne : g ≠ f := fun h => hf (h ▸ hg)
    have hmem := ((Xi.faceBoundary (E.faces g)).mem_iff x).mpr hgx.symm
    rw [E.face_boundary g hne] at hmem
    obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hmem
    exact ⟨d, hdx, ((Delta.faceBoundary g).mem_iff d).mp hd ▸ hg⟩
  · rintro ⟨d, rfl, hd⟩
    have hne : Delta.toCombMap.faceOf d ≠ f := fun h => hf (h ▸ hd)
    apply Finset.mem_map.mpr
    refine ⟨Delta.toCombMap.faceOf d, hd, ?_⟩
    symm
    apply ((Xi.faceBoundary (E.faces (Delta.toCombMap.faceOf d))).mem_iff _).mp
    rw [E.face_boundary _ hne]
    exact List.mem_map.mpr ⟨d, ((Delta.faceBoundary _).mem_iff d).mpr rfl, rfl⟩

theorem faceOf_dart_mem_iff (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (d : Delta.toCombMap.Dart) :
    Xi.toCombMap.faceOf (E.darts d) ∈ E.faceSet s ↔ Delta.toCombMap.faceOf d ∈ s := by
  rw [E.faceOf_mem_iff s hf]
  constructor
  · rintro ⟨e, he, hemem⟩
    exact E.darts.injective he ▸ hemem
  · intro hd
    exact ⟨d, rfl, hd⟩

theorem isBoundaryDart_iff (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (d : Delta.toCombMap.Dart) :
    IsBoundaryDart Xi (E.faceSet s) (E.darts d) ↔ IsBoundaryDart Delta s d := by
  simp only [IsBoundaryDart, E.alpha, E.faceOf_dart_mem_iff s hf]

theorem boundary_dart_iff (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (x : Xi.toCombMap.Dart) :
    IsBoundaryDart Xi (E.faceSet s) x ↔
      ∃ d : Delta.toCombMap.Dart, E.darts d = x ∧ IsBoundaryDart Delta s d := by
  constructor
  · intro hx
    obtain ⟨d, hd, _⟩ := (E.faceOf_mem_iff s hf x).mp hx.1
    exact ⟨d, hd, (E.isBoundaryDart_iff s hf d).mp (hd.symm ▸ hx)⟩
  · rintro ⟨d, rfl, hd⟩
    exact (E.isBoundaryDart_iff s hf d).mpr hd

theorem internal_move (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    {d e : Delta.toCombMap.Dart} (h : InternalBoundaryMove Delta s d e) :
    InternalBoundaryMove Xi (E.faceSet s) (E.darts d) (E.darts e) := by
  refine ⟨(E.faceOf_dart_mem_iff s hf d).mpr h.1, ?_, ?_⟩
  · rw [E.alpha]
    exact (E.faceOf_dart_mem_iff s hf _).mpr h.2.1
  · rw [E.alpha, E.facePerm _ (fun heq => hf (heq ▸ h.2.1))]
    exact congrArg E.darts h.2.2

theorem boundary_step (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    {d e : Delta.toCombMap.Dart} (h : BoundaryStep Delta s d e) :
    BoundaryStep Xi (E.faceSet s) (E.darts d) (E.darts e) := by
  refine ⟨(E.isBoundaryDart_iff s hf d).mpr h.1,
    (E.isBoundaryDart_iff s hf e).mpr h.2.1, ?_⟩
  rw [E.facePerm d (fun heq => hf (heq ▸ h.1.1))]
  exact h.2.2.lift E.darts (fun _ _ hm => E.internal_move s hf hm)

/-- The same cyclic list, with the same length and order, bounds the retained region. -/
def boundary (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (B : FaceSetBoundary Delta s) : FaceSetBoundary Xi (E.faceSet s) where
  faces_nonempty := by
    obtain ⟨g, hg⟩ := B.faces_nonempty
    exact ⟨E.faces g, Finset.mem_map.mpr ⟨g, hg, rfl⟩⟩
  all_gCells := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hg
    refine ⟨?_, ?_⟩
    · rw [E.outer]
      exact fun heq => (B.all_gCells h hh).1 (E.faces.injective heq)
    · rw [E.faceWord_eq h (fun heq => hf (heq ▸ hh))]
      exact (B.all_gCells h hh).2
  cycle := B.cycle.map E.darts
  cycle_nonempty := fun h => B.cycle_nonempty (List.map_eq_nil_iff.mp h)
  cycle_nodup := B.cycle_nodup.map E.darts.injective
  cycle_mem_iff := by
    intro d
    rw [E.boundary_dart_iff s hf d, List.mem_map]
    constructor
    · rintro ⟨e, he, hed⟩
      exact ⟨e, hed, (B.cycle_mem_iff e).mp he⟩
    · rintro ⟨e, hed, he⟩
      exact ⟨e, (B.cycle_mem_iff e).mpr he, hed⟩
  cycle_chain := by
    rw [List.isChain_map]
    exact B.cycle_chain.imp (fun _ _ h => E.boundary_step s hf h)
  cycle_closes := by
    rw [List.getLast_map, List.head_map]
    exact E.boundary_step s hf B.cycle_closes

theorem invDarts_map (l : List Delta.toCombMap.Dart) :
    invDarts Xi (l.map E.darts) = (invDarts Delta l).map E.darts := by
  simp only [invDarts, List.map_reverse, List.map_map]
  exact congrArg List.reverse (List.map_congr_left (fun d _ => E.alpha d))

/-- Preserve the actual face-shelling witness, with every attaching arc unchanged. -/
theorem shelling (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    {l : List Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart}
    (H : FaceShelling Delta s l cycle) :
    FaceShelling Xi (E.faceSet s) (l.map E.faces) (cycle.map E.darts) := by
  induction H with
  | empty => exact FaceShelling.empty
  | @step l before arc after exposed g hg k hrot rest ih =>
    simp only [List.map_cons, List.map_append] at ih ⊢
    apply FaceShelling.step (E.faces g) (Finset.mem_map.mpr ⟨g, hg, rfl⟩) k
    · rw [E.face_boundary g (fun heq => hf (heq ▸ hg)), ← List.map_rotate,
        hrot, List.map_append, E.invDarts_map]
    · exact ih

end DiscEmbeddingAway
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.boundary
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.shelling
