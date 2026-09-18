import GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWind
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: a first excision step always exists

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-59.

Route.  Part (d) of the winding choice (`gfaceWind_Choice`, `Piece10Live/GFaceWind`) asks for a
nonempty excision sequence.  A walk `c` that repeats a vertex has an innermost lobe
`c = p ++ A ++ q` with `A` a closed dart walk repeating no vertex
(`ClosedWalkInnermostLobe.exists_innermost_lobe`); when no dart of `c` has its reverse on `c`,
`A` is a simple closed walk, so the inner excision of `A` is a winding step
(`gfaceWindFive_step`).  On a pocket, `¬Unpinched` says exactly that the walk repeats a vertex
(`gfaceWindFive_not_nodup`), and boundary darts never pair with their reverses, so the start
state `(K.boundary.cycle, [· ∈ K.faces])` has a winding step, and its target satisfies the
invariant and is strictly shorter (`gfaceWindFive_pocket_step`, `gfaceWindFive_reach`).

* `gfaceWindFive_lobe` (proved): a simple closed stretch of a pinched alpha-free walk.
* `gfaceWindFive_step` (proved): a winding step from any state whose walk is pinched.
* `gfaceWindFive_not_nodup` (proved): `¬Unpinched` gives a repeated vertex on the walk.
* `gfaceWindFive_pocket_step`, `gfaceWindFive_reach` (proved): a nonempty excision sequence
  from the start state of a pocket, with the invariant.

What is NOT proved here: that some such sequence ends in a `0/1`-valued `g` with a cell in its
support (the rest of part (d)); the one-step state of the innermost lobe is `0/1`-valued only in
the loop cases of `Piece10Live/GFaceChooseLoop`.

## Truth check

All statements here are proved (no hypothesis Props).  Consistent with the models of
`gl-p10-55/wind.py`: every premise-satisfying pocket there has a reached state.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **A simple closed stretch of a pinched walk**: a walk with no dart reversed on it that
repeats a vertex has a consecutive stretch that is a simple closed walk. -/
theorem gfaceWindFive_lobe {M : CombMap.{v}} {c : List M.Dart}
    (hch : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hal : ∀ x ∈ c, M.alpha x ∉ c) (hrep : ¬ (c.map M.vertexOf).Nodup) :
    ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A := by
  obtain ⟨p, A, q, hseg, ⟨hne, hchA, hcl⟩, hnd⟩ :=
    ClosedWalkInnermostLobe.exists_innermost_lobe hch hrep
  have hsub : ∀ x ∈ A, x ∈ c := fun x hx => by
    rw [hseg]
    exact List.mem_append_left q (List.mem_append_right p hx)
  exact ⟨p, A, q, hseg,
    ⟨hne, hchA, hcl, hnd, fun x hx hax => hal x (hsub x hx) (hsub _ hax)⟩⟩

/-- **A winding step from a pinched state**: the inner excision of the innermost lobe. -/
theorem gfaceWindFive_step {M : CombMap.{v}} (o : M.Face) {c : List M.Dart}
    (g : M.Face → ℤ) (hch : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hal : ∀ x ∈ c, M.alpha x ∉ c) (hrep : ¬ (c.map M.vertexOf).Nodup) :
    ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t := by
  obtain ⟨p, A, q, hseg, hw⟩ := gfaceWindFive_lobe hch hal hrep
  exact ⟨(p ++ q, fun f => g f - gfaceWind_wind M o A f), p, A, q, hseg,
    Or.inl ⟨hw, rfl, rfl⟩⟩

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pinched pocket walk repeats a vertex.** -/
theorem gfaceWindFive_not_nodup (K : PocketFaceSet D eps X lo hi)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ¬ (K.boundary.cycle.map X.toCombMap.vertexOf).Nodup := by
  intro hnd
  apply hpinch
  intro x y hx hy hxy
  exact List.inj_on_of_nodup_map hnd ((K.boundary.cycle_mem_iff x).mpr hx)
    ((K.boundary.cycle_mem_iff y).mpr hy) hxy

/-- **A first excision step of a pinched pocket**, with the invariant and a shorter walk. -/
theorem gfaceWindFive_pocket_step (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ∃ t : List X.toCombMap.Dart × (X.toCombMap.Face → ℤ),
      gfaceWind_Step X.toCombMap X.outerFace (K.boundary.cycle, gfaceWind_ind K.faces) t ∧
      gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace t.1 t.2 ∧
      t.1.length < K.boundary.cycle.length := by
  have hc := K.boundary.cycle_mem_iff
  have hal : ∀ x ∈ K.boundary.cycle, X.toCombMap.alpha x ∉ K.boundary.cycle :=
    fun x hx hax => ((hc x).mp hx).2 ((hc _).mp hax).1
  obtain ⟨t, ht⟩ := gfaceWindFive_step X.outerFace (gfaceWind_ind K.faces) hK.1 hal
    (gfaceWindFive_not_nodup K hpinch)
  have h0 : gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace K.boundary.cycle
      (gfaceWind_ind K.faces) :=
    gfaceWind_inv_start (fun d => (hc d).symm) hK.1 K.outerFace_not_mem
  exact ⟨t, ht, gfaceWind_step_inv (s := (K.boundary.cycle, gfaceWind_ind K.faces)) (t := t)
    X.planar K.boundary.cycle_nodup h0 ht⟩

/-- **A nonempty excision sequence of a pinched pocket**, with the invariant. -/
theorem gfaceWindFive_reach (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
      Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
        (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧
      gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace c g ∧
      c.length < K.boundary.cycle.length := by
  obtain ⟨⟨c, g⟩, ht, hinv, hlen⟩ := gfaceWindFive_pocket_step K hK hpinch
  exact ⟨c, g, Relation.TransGen.single ht, hinv, hlen⟩

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_not_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_pocket_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_reach
