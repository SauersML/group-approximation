import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeMirror
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusStatement
import GroupApproximation.GGT.VanKampen.SurgeryFaceNew
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-61: boundary darts lifted to the reclosed mirror

Lane gl-p07-61.  Certifies no printed sentence on its own.  NOT COMPILED.

Let `B` be a boundary cycle of a face set `O` of a map `M`.  A list `L` of boundary darts of `O`
lifts to kept darts, and `witnessStepBridge_liftList` reverses it and reads it through `α`.
* `witnessStepBridge_liftList_map`: the lift reads back as `L.reverse.map α`, the `invDarts`
  form of `L`.
* `witnessStepBridge_reclosed_isFaceCycle`: the lift of `B.cycle` is a face cycle of the mirror of
  the reclosed map, when `B` follows the boundary and `M` is planar.
* `witnessStepBridge_before_map`: an injective map preserves and reflects the order of a list.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe v

open Surgery.MapCollapse

namespace FourPieceWitness

/-- An injective map preserves and reflects the order of a list. -/
theorem witnessStepBridge_before_map {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {L : List α} {c d : α} :
    WitnessStepGenusBefore (L.map f) (f c) (f d) ↔ WitnessStepGenusBefore L c d := by
  constructor
  · rintro ⟨u, v, z, h⟩
    obtain ⟨l₁, l₂, rfl, -, h₃⟩ := List.map_eq_append_iff.mp h
    obtain ⟨c', r, rfl, hc, hr⟩ := List.map_eq_cons_iff.mp h₃
    obtain ⟨r₁, r₂, rfl, -, h₄⟩ := List.map_eq_append_iff.mp hr
    obtain ⟨d', z', rfl, hd, -⟩ := List.map_eq_cons_iff.mp h₄
    rw [hf hc, hf hd]
    exact ⟨l₁, r₁, z', rfl⟩
  · rintro ⟨u, v, z, rfl⟩
    exact ⟨u.map f, v.map f, z.map f, by simp only [List.map_append, List.map_cons]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_before_map

/-- A rotation step of a list, read through a map. -/
theorem witnessStepBridge_rotate_val {α β : Type*} {f : α → β} {l : List α} {L : List β}
    {n : ℕ} {s t : List α} {c d : α} (hmap : l.map f = L)
    (h : l.rotate n = s ++ c :: d :: t) :
    L.rotate n = s.map f ++ f c :: f d :: t.map f := by
  rw [← hmap, ← List.map_rotate, h, List.map_append, List.map_cons, List.map_cons]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_rotate_val

/-- **The lift of a list of boundary darts**, reversed and read through `α`, as kept darts. -/
def witnessStepBridge_liftList (M : CombMap.{v}) (O : Finset M.Face) (L : List M.Dart)
    (H : ∀ d ∈ L, Surgery.MapCollapse.IsBoundaryDart M O d) : List (KeptDart M O) :=
  (L.pmap (keptDartOfIsBoundary M O) H).reverse.map (keptAlpha M O)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_liftList

/-- The lift reads back as the reverse of the list through `α`. -/
theorem witnessStepBridge_liftList_map (M : CombMap.{v}) (O : Finset M.Face) (L : List M.Dart)
    (H : ∀ d ∈ L, Surgery.MapCollapse.IsBoundaryDart M O d) :
    (witnessStepBridge_liftList M O L H).map Subtype.val = L.reverse.map M.alpha := by
  have hp : (L.pmap (keptDartOfIsBoundary M O) H).map Subtype.val = L := by
    rw [List.map_pmap]
    exact List.pmap_eq_self.mpr fun _ _ => rfl
  calc (witnessStepBridge_liftList M O L H).map Subtype.val
      = (L.pmap (keptDartOfIsBoundary M O) H).reverse.map (Subtype.val ∘ keptAlpha M O) :=
        List.map_map
    _ = (L.pmap (keptDartOfIsBoundary M O) H).reverse.map (M.alpha ∘ Subtype.val) := rfl
    _ = ((L.pmap (keptDartOfIsBoundary M O) H).reverse.map Subtype.val).map M.alpha :=
        List.map_map.symm
    _ = ((L.pmap (keptDartOfIsBoundary M O) H).map Subtype.val).reverse.map M.alpha :=
        congrArg (List.map M.alpha) List.map_reverse
    _ = L.reverse.map M.alpha := by rw [hp]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_liftList_map

/-- The reverse of an entry of the lift lies on the list. -/
theorem witnessStepBridge_liftList_mem (M : CombMap.{v}) (O : Finset M.Face) (L : List M.Dart)
    (H : ∀ d ∈ L, Surgery.MapCollapse.IsBoundaryDart M O d) (z : KeptDart M O)
    (hz : z ∈ witnessStepBridge_liftList M O L H) : M.alpha z.1 ∈ L := by
  have h1 : z.1 ∈ L.reverse.map M.alpha := by
    rw [← witnessStepBridge_liftList_map M O L H]
    exact List.mem_map_of_mem hz
  obtain ⟨o, ho, hoz⟩ := List.mem_map.mp h1
  rw [← hoz, M.alpha_involutive o]
  exact List.mem_reverse.mp ho

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_liftList_mem

/-- The lift is monotone in the list. -/
theorem witnessStepBridge_liftList_subset (M : CombMap.{v}) (O : Finset M.Face)
    (L L' : List M.Dart) (H : ∀ d ∈ L, Surgery.MapCollapse.IsBoundaryDart M O d)
    (H' : ∀ d ∈ L', Surgery.MapCollapse.IsBoundaryDart M O d) (hLL : ∀ o ∈ L, o ∈ L') :
    ∀ z ∈ witnessStepBridge_liftList M O L H, z ∈ witnessStepBridge_liftList M O L' H' := by
  intro z hz
  have h1 : z.1 ∈ L'.reverse.map M.alpha :=
    List.mem_map.mpr ⟨M.alpha z.1,
      List.mem_reverse.mpr (hLL _ (witnessStepBridge_liftList_mem M O L H z hz)),
      M.alpha_involutive z.1⟩
  rw [← witnessStepBridge_liftList_map M O L' H', List.mem_map] at h1
  obtain ⟨g, hg, hgz⟩ := h1
  rw [← Subtype.ext hgz]
  exact hg

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_liftList_subset

/-- **The lifted boundary cycle is a face cycle of the reclosed mirror.** -/
theorem witnessStepBridge_reclosed_isFaceCycle (M : CombMap.{v}) (O : Finset M.Face)
    (B : BoundaryCycle M O) (hwalk : B.FollowsBoundary) (hM : M.IsPlanar) :
    (witnessStepBridge_mirror (reclosedMap M O B)).IsFaceCycle
      (witnessStepBridge_liftList M O B.cycle (isBoundaryDart_of_mem_cycle M O B)) := by
  have h0 : (reclosedMap M O B).IsFaceCycle (newFaceDarts M O B) :=
    ⟨newFaceDarts_ne_nil M O B, newFaceDarts_nodup M O B,
      newFaceDarts_chain M O (BoundaryCycle.toDiscRegion_of_followsBoundary M O B hwalk hM),
      newFaceDarts_closes M O (BoundaryCycle.toDiscRegion_of_followsBoundary M O B hwalk hM)⟩
  exact witnessStepBridge_mirror_isFaceCycle _ h0

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_reclosed_isFaceCycle

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
