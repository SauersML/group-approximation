import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Convert
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryCircuits
import GroupApproximation.Meta.AxiomGuard

/-!
# Boundary darts of a face set are balanced at every vertex

A classical fact about the boundary 1-chain of a face set in a combinatorial map: at every vertex,
as many boundary darts start as end.  It is a generic tool for the rose step of Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): a list enumerating the boundary darts of a face
set is balanced, so an Euler re-listing turns it into a closed dart walk.

## Conventions

A dart `d` starts at `M.vertexOf d` and ends at `M.vertexOf (M.alpha d)` (the convention of
`IsClosedDartWalk`).  `Surgery.MapCollapse.IsBoundaryDart M F d` says `d` is based in a face of `F`
and its reverse is not.

## Proof

`FaceSetCircuits.boundaryPerm M F` (`FaceSetBoundaryCircuits.lean:120`) is a permutation of the
boundary darts, and `boundaryPerm_walk` (`:130`) gives `BoundaryWalk M F d (boundaryPerm d)`:
starting from `facePerm d = sigma (alpha d)`, a run of `sigma` steps reaches `boundaryPerm d`.
Every `sigma` step preserves the vertex, so `vertexOf (boundaryPerm d) = vertexOf (alpha d)`
(`vertexOf_boundaryPerm`): each boundary dart ends where its successor starts.  Hence `boundaryPerm`
maps the boundary darts ending at `x` bijectively onto the boundary darts starting at `x`, with
inverse `boundaryPerm.symm`; `Finset.card_bij'` gives `boundary_balanced`.

For the list form, a duplicate-free list `c` whose members are exactly the boundary darts has
`c.countP (fun d => decide (g d = x))` equal to the cardinality of the boundary darts with
`g d = x` (`countP_eq_card_filter`, through `List.toFinset_card_of_nodup`); apply it with
`g = vertexOf` and `g = vertexOf ∘ alpha`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance

universe v

open Surgery.MapCollapse

/-- A boundary walk from `d` ends at the vertex where `d` ends: the walk starts at
`facePerm d = sigma (alpha d)` and only takes `sigma` steps. -/
theorem vertexOf_alpha_eq_of_boundaryWalk {M : CombMap.{v}} {F : Finset M.Face} {d e : M.Dart}
    (h : BoundaryWalk M F d e) : M.vertexOf (M.alpha d) = M.vertexOf e := by
  unfold BoundaryWalk at h
  induction h with
  | refl => exact (M.vertexOf_sigma (M.alpha d)).symm
  | tail _ hstep ih => rw [ih, ← hstep.2, M.vertexOf_sigma]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance.vertexOf_alpha_eq_of_boundaryWalk

/-- The boundary successor of a boundary dart starts where the dart ends. -/
theorem vertexOf_boundaryPerm (M : CombMap.{v}) (F : Finset M.Face) (b : BoundaryDart M F) :
    M.vertexOf (FaceSetCircuits.boundaryPerm M F b).1 = M.vertexOf (M.alpha b.1) :=
  (vertexOf_alpha_eq_of_boundaryWalk (FaceSetCircuits.boundaryPerm_walk M F b)).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance.vertexOf_boundaryPerm

/-- The boundary predecessor of a boundary dart ends where the dart starts. -/
theorem vertexOf_alpha_boundaryPerm_symm (M : CombMap.{v}) (F : Finset M.Face)
    (b : BoundaryDart M F) :
    M.vertexOf (M.alpha ((FaceSetCircuits.boundaryPerm M F).symm b).1) = M.vertexOf b.1 := by
  have h := vertexOf_boundaryPerm M F ((FaceSetCircuits.boundaryPerm M F).symm b)
  rw [Equiv.apply_symm_apply (FaceSetCircuits.boundaryPerm M F) b] at h
  exact h.symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance.vertexOf_alpha_boundaryPerm_symm

open Classical in
/-- **Boundary darts are balanced.**  At every vertex `x`, the boundary darts of the face set `F`
starting at `x` are as many as those ending at `x`. -/
theorem boundary_balanced (M : CombMap.{v}) (F : Finset M.Face) (x : M.Vertex) :
    (Finset.univ.filter (fun d => Surgery.MapCollapse.IsBoundaryDart M F d ∧
        M.vertexOf d = x)).card =
      (Finset.univ.filter (fun d => Surgery.MapCollapse.IsBoundaryDart M F d ∧
        M.vertexOf (M.alpha d) = x)).card := by
  refine Finset.card_bij'
    (s := Finset.univ.filter (fun d => Surgery.MapCollapse.IsBoundaryDart M F d ∧
        M.vertexOf d = x))
    (t := Finset.univ.filter (fun d => Surgery.MapCollapse.IsBoundaryDart M F d ∧
        M.vertexOf (M.alpha d) = x))
    (fun a ha => ((FaceSetCircuits.boundaryPerm M F).symm
      ⟨a, (Finset.mem_filter.mp ha).2.1⟩).1)
    (fun b hb => (FaceSetCircuits.boundaryPerm M F ⟨b, (Finset.mem_filter.mp hb).2.1⟩).1)
    ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((FaceSetCircuits.boundaryPerm M F).symm ⟨a, (Finset.mem_filter.mp ha).2.1⟩).2,
      (vertexOf_alpha_boundaryPerm_symm M F ⟨a, (Finset.mem_filter.mp ha).2.1⟩).trans
        (Finset.mem_filter.mp ha).2.2⟩
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (FaceSetCircuits.boundaryPerm M F ⟨b, (Finset.mem_filter.mp hb).2.1⟩).2,
      (vertexOf_boundaryPerm M F ⟨b, (Finset.mem_filter.mp hb).2.1⟩).trans
        (Finset.mem_filter.mp hb).2.2⟩
  · intro a ha
    exact congrArg Subtype.val (Equiv.apply_symm_apply (FaceSetCircuits.boundaryPerm M F)
      ⟨a, (Finset.mem_filter.mp ha).2.1⟩)
  · intro b hb
    exact congrArg Subtype.val (Equiv.symm_apply_apply (FaceSetCircuits.boundaryPerm M F)
      ⟨b, (Finset.mem_filter.mp hb).2.1⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance.boundary_balanced

open Classical in
/-- A duplicate-free list of exactly the boundary darts counts the boundary darts with a given
vertex label. -/
theorem countP_eq_card_filter {M : CombMap.{v}} {F : Finset M.Face} [DecidableEq M.Vertex]
    {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) (g : M.Dart → M.Vertex)
    (x : M.Vertex) :
    c.countP (fun d => decide (g d = x)) =
      (Finset.univ.filter (fun d => Surgery.MapCollapse.IsBoundaryDart M F d ∧
        g d = x)).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnodup.filter _)]
  congr 1
  ext d
  constructor
  · intro hd
    obtain ⟨hdc, hdx⟩ := List.mem_filter.mp (List.mem_toFinset.mp hd)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ d, (hc d).mp hdc, of_decide_eq_true hdx⟩
  · intro hd
    obtain ⟨-, hdb, hdx⟩ := Finset.mem_filter.mp hd
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(hc d).mpr hdb, decide_eq_true hdx⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance.countP_eq_card_filter

/-- **List form.**  A duplicate-free list whose members are exactly the boundary darts of `F` has,
at every vertex `x`, as many darts starting at `x` as ending at `x`. -/
theorem boundary_countP_balanced {M : CombMap.{v}} {F : Finset M.Face} [DecidableEq M.Vertex]
    {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) (x : M.Vertex) :
    c.countP (fun d => decide (M.vertexOf d = x)) =
      c.countP (fun d => decide (M.vertexOf (M.alpha d) = x)) := by
  refine (countP_eq_card_filter hnodup hc M.vertexOf x).trans ?_
  refine Eq.trans ?_ (countP_eq_card_filter hnodup hc (fun d => M.vertexOf (M.alpha d)) x).symm
  convert boundary_balanced M F x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance.boundary_countP_balanced

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseBalance
