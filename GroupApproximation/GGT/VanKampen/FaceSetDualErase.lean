import GroupApproximation.GGT.VanKampen.FaceSetDualReach
import GroupApproximation.GGT.VanKampen.FaceSetDualWalk

/-!
# Some selected face can be deleted without disconnecting the dual

This is the first half of the extremal-face step: a selected face set with more
than one face has a face whose deletion leaves the selected dual connected.  It
is the leaf of a spanning tree of the dual graph, obtained from the finite
removable-point theorem together with the dual connectivity proved in
`FaceSetDualReach`.

It is not yet an ear.  Knowing that `faces.erase f` is dual-connected does not
by itself say that its boundary is a single cycle, which is where the planar
Euler input is still needed.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

/-- A bounded walk inside a carrier gives an equivalence-closure connection for
any relation dominating the steps between carrier points. -/
theorem eqvGen_of_reachIn {α : Type u} {s : Finset α} {r r' : α → α → Prop}
    (hup : ∀ x y : α, x ∈ s → y ∈ s → r x y → r' x y) :
    ∀ (n : ℕ) (a b : α), a ∈ s → b ∈ s → ReachIn s r n a b →
      Relation.EqvGen r' a b := by
  intro n
  induction n with
  | zero =>
      intro a b _ _ h
      rw [reachIn_zero_iff.mp h]
      exact Relation.EqvGen.refl _
  | succ n ih =>
      intro a b ha hb h
      rcases reachIn_succ_iff.mp h with h | h
      · exact ih a b ha hb h
      · obtain ⟨c, hc, hac, hcb⟩ := h
        exact Relation.EqvGen.trans _ _ _ (ih a c ha hc hac)
          (Relation.EqvGen.rel _ _ (hup c b hc hb hcb))

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqDualErase :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-- Dual adjacency is symmetric: read the shared edge from the other side. -/
theorem dualAdjacency_symm
    {faces : Finset Delta.toCombMap.Face}
    {f g : Delta.toCombMap.Face} (h : DualAdjacency Delta faces f g) :
    DualAdjacency Delta faces g f := by
  obtain ⟨hf, hg, d, hd, hda⟩ := h
  refine ⟨hg, hf, Delta.toCombMap.alpha d, hda, ?_⟩
  rw [Delta.toCombMap.alpha_involutive]
  exact hd

/-- Dual adjacency of two faces of a smaller selected set is dual adjacency for
that smaller set: the shared edge is the same. -/
theorem dualAdjacency_mono
    {faces small : Finset Delta.toCombMap.Face}
    {f g : Delta.toCombMap.Face} (hf : f ∈ small) (hg : g ∈ small)
    (h : DualAdjacency Delta faces f g) :
    DualAdjacency Delta small f g := by
  obtain ⟨_, _, d, hd, hda⟩ := h
  exact ⟨hf, hg, d, hd, hda⟩

/-- A selected face set with more than one face has a face whose deletion
leaves the selected dual connected. -/
theorem exists_erase_dualConnected
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (hcard : 1 < faces.card) :
    ∃ f, f ∈ faces ∧
      ∀ g ∈ faces.erase f, ∀ g' ∈ faces.erase f,
        Relation.EqvGen (DualAdjacency Delta (faces.erase f)) g g' := by
  obtain ⟨root, hroot⟩ := boundary.faces_nonempty
  obtain ⟨f, hf, hfroot, hreach⟩ :=
    exists_erase_eqvGen faces (DualAdjacency Delta faces)
      (fun _ _ h => dualAdjacency_symm h)
      (fun _ _ h => h.1) (fun _ _ h => h.2.1)
      root hroot
      (fun b hb => dualFaces_connected boundary hroot hb) hcard
  refine ⟨f, hf, ?_⟩
  have hrootmem : root ∈ faces.erase f :=
    Finset.mem_erase.mpr ⟨fun hcon => hfroot hcon.symm, hroot⟩
  have hconn : ∀ g ∈ faces.erase f,
      Relation.EqvGen (DualAdjacency Delta (faces.erase f)) root g := by
    intro g hg
    obtain ⟨n, hn⟩ := hreach g (Finset.mem_of_mem_erase hg)
      (Finset.mem_erase.mp hg).1
    exact eqvGen_of_reachIn
      (fun x y hx hy hxy => dualAdjacency_mono hx hy hxy) n root g
      hrootmem hg hn
  intro g hg g' hg'
  exact Relation.EqvGen.trans _ _ _ (hconn g hg).symm (hconn g' hg')

end Embedded
end VanKampen
end GGT
end GroupApproximation
