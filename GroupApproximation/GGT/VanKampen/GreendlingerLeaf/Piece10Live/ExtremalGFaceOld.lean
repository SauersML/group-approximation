import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalGFace
import GroupApproximation.Meta.AxiomGuard

/-!
# The single-class block statement implies the G-face tolerant flip statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-47.

The colouring `z := regionColour r` of one walk region turns the single-class no-wrap block
clauses `P10ExtremalWrap.ExtremalBlockNoWrapClauses K r kept` into `extremalGFace_Clauses K z`:
constancy is `regionColour_step`, the side-pair clause is `regionColour_indep`, the exterior
clause is `not_mem_flipFaces`, and a cycle dart touching the region exists in a connected map
(`P10RegionMove.exists_mem_eqvGen_of_connected`).  So `extremalGFace_Statement` is implied by
`P10ExtremalWrap.RoseExtremalBlockNoWrapStatement` (`extremalGFace_of_blockNoWrap`).

The converse fails: in the gl-p10-40 model the single-class statement fails and the G-face
tolerant one holds (with `z` marking four regions), so `extremalGFace_Statement` is strictly
weaker.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The G-face tolerant clauses from the single-class no-wrap block clauses**, at the colouring
of the region of `r`. -/
theorem extremalGFace_clauses_of_blockNoWrapClauses (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} {kept : Fin X.rCellCount} (h : ExtremalBlockNoWrapClauses K r kept) :
    extremalGFace_Clauses K
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) := by
  obtain ⟨hrout, hsource, hkept, hne, hch, hblk₁, hblk₂⟩ := h
  have hz := regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
  obtain ⟨y, hy, hry⟩ := P10RegionMove.exists_mem_eqvGen_of_connected
    (CombMap.connected_of_planar X.toCombMap X.planar) K.boundary.cycle_nonempty r
  exact ⟨hz, regionColour_indep K.boundary.cycle_mem_iff r,
    not_mem_flipFaces hz K.outerFace_not_mem
      (fun x hx => regionColour_eq_false X.toCombMap _ (hrout x hx)),
    hsource, ⟨kept, hkept⟩, ⟨y, hy, movePred_regionColour_eq_false hry⟩, hne, hch, hblk₁, hblk₂⟩

end Clauses

/-- **The G-face tolerant flip statement from the single-class no-wrap block statement.** -/
theorem extremalGFace_of_blockNoWrap (h : RoseExtremalBlockNoWrapStatement.{u, w, v}) :
    extremalGFace_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hc⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r,
    extremalGFace_clauses_of_blockNoWrapClauses (kept := kept) K hc⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_clauses_of_blockNoWrapClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_of_blockNoWrap
