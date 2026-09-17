import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.Grow
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler re-listing of a balanced connected dart list (lane gl-p10-06)

* `exists_perm_closedTrail`: a nonempty balanced list whose entries are connected through shared
  vertices can be re-listed as a closed trail (Hierholzer).  Extract a first closed trail through
  the head entry (`exists_closedTrail_head`), then grow it (`exists_perm_closedTrail_grow`).
* `exists_perm_isClosedDartWalk`: the same for darts of a combinatorial map, with start label
  `M.vertexOf` and end label `fun d => M.vertexOf (M.alpha d)`.  `IsClosedDartWalk M` is
  `IsClosedTrail` for these labels by definition.
* `isClosedDartWalk_splice`: splicing a closed dart walk into another at a shared vertex
  (`IsClosedTrail.splice`).

The statement of `exists_perm_isClosedDartWalk` carries `[DecidableEq M.Vertex]`, which the
`decide` in the balance hypothesis needs (the lane pitfall note: `M.Vertex` has no global
decidable equality).  This is more general than fixing a classical instance.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler

universe v

section Generic

variable {α V : Type*} {s t : α → V}

/-- **Euler re-listing (generic).**  A nonempty balanced list whose entries are connected through
shared vertices is a permutation of a closed trail. -/
theorem exists_perm_closedTrail [DecidableEq V] (L : List α) (hne : L ≠ [])
    (hbal : IsBalanced s t L)
    (hconn : ∀ d ∈ L, ∀ e ∈ L, Relation.ReflTransGen
      (fun a b => a ∈ L ∧ b ∈ L ∧ (t a = s b ∨ s b = t a ∨ s a = s b ∨ t a = t b)) d e) :
    ∃ L' : List α, L'.Perm L ∧ IsClosedTrail s t L' := by
  obtain ⟨C, R, _, hC, _, hCperm⟩ := exists_closedTrail_head hbal (List.head_mem hne)
  exact exists_perm_closedTrail_grow hconn R.length C R rfl hC hCperm
    (IsBalanced.cancel_left (hbal.perm hCperm.symm) hC.isBalanced)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.exists_perm_closedTrail

end Generic

/-- **Euler re-listing of darts.**  A nonempty dart list in which every vertex is as often a start
as an end, and whose darts are connected through shared vertices, is a permutation of a closed
dart walk. -/
theorem exists_perm_isClosedDartWalk {M : CombMap.{v}} [DecidableEq M.Vertex] (L : List M.Dart)
    (hne : L ≠ [])
    (hbal : ∀ x : M.Vertex, L.countP (fun d => decide (M.vertexOf d = x)) =
      L.countP (fun d => decide (M.vertexOf (M.alpha d) = x)))
    (hconn : ∀ d ∈ L, ∀ e ∈ L, Relation.ReflTransGen
      (fun a b => a ∈ L ∧ b ∈ L ∧ (M.vertexOf (M.alpha a) = M.vertexOf b ∨
        M.vertexOf b = M.vertexOf (M.alpha a) ∨ M.vertexOf a = M.vertexOf b ∨
        M.vertexOf (M.alpha a) = M.vertexOf (M.alpha b))) d e) :
    ∃ L', L'.Perm L ∧ IsClosedDartWalk M L' := by
  obtain ⟨L', hp, hL'⟩ := exists_perm_closedTrail (s := M.vertexOf)
    (t := fun d => M.vertexOf (M.alpha d)) L hne hbal hconn
  exact ⟨L', hp, hL'⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.exists_perm_isClosedDartWalk

/-- **Splicing closed dart walks.**  If `A ++ B` and `C` are closed dart walks and the last dart of
`A` ends where `C` starts, then `A ++ C ++ B` is a closed dart walk. -/
theorem isClosedDartWalk_splice {M : CombMap.{v}} {A B C : List M.Dart}
    (hAB : IsClosedDartWalk M (A ++ B)) (hC : IsClosedDartWalk M C) (hA : A ≠ []) (hC0 : C ≠ [])
    (hv : M.vertexOf (M.alpha (A.getLast hA)) = M.vertexOf (C.head hC0)) :
    IsClosedDartWalk M (A ++ C ++ B) :=
  IsClosedTrail.splice (s := M.vertexOf) (t := fun d => M.vertexOf (M.alpha d)) hAB hC hA hC0 hv

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.isClosedDartWalk_splice

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler
