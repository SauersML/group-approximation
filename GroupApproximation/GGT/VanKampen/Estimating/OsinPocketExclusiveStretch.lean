import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketExclusiveWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoinsBoundaryArc
import GroupApproximation.GGT.VanKampen.FaceSetCircuitNoncrossing
import GroupApproximation.Meta.AxiomGuard

/-!
# The four stretches of the exclusive pocket tour

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.7(b).  Route
`research/nm-exclusive-pocket-first-turns.md`, tour algebra `Estimating/OsinPocketExclusiveTour`.

The complement side of the exclusive pocket of two exterior regions `x`, `y` of the cell `Π` is a
tour around `U = x ∪ y ∪ {Π, exterior}` made of four stretches, each a chain of boundary walks:

* along `x`: from the last target dart of `x`, along its left side, to its first reversed
  source dart (`isChain_leftStretch`, crossing the base point of the cycle of `x`);
* along `Π`: from the last dart of the source arc of `x`, along the gap arc, to the first dart of
  the source arc of `y` (`isChain_cellStretch`);
* along `y`: from the last reversed source dart of `y`, along its right side, to its first target
  dart (`isChain_rightStretch`);
* along `∂Δ`: from the first target dart of `y` read backwards, along the stretch of `∂Δ` between
  the target arcs read backwards, to the last target dart of `x` read backwards
  (`isChain_outerStretch`).

This module proves the four chain statements from the region cycles, the face boundary of `Π` and
the oriented outer boundary.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC

namespace ExclusiveStretch

/-- **The middle of a chain between two nonempty ends**: the last element of `A`, then `G`, then
the first element of `B`. -/
theorem isChain_middle {α : Type*} {R : α → α → Prop} {A G B : List α} (hA : A ≠ [])
    (hB : B ≠ []) (h : (A ++ G ++ B).IsChain R) :
    (A.getLast hA :: G ++ [B.head hB]).IsChain R := by
  have heq : A ++ G ++ B = A.dropLast ++ ((A.getLast hA :: G ++ [B.head hB]) ++ B.tail) := by
    conv_lhs => rw [← List.dropLast_append_getLast hA, ← List.cons_head_tail hB]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [heq] at h
  exact (List.isChain_append.mp (List.isChain_append.mp h).2.1).1

/-- The closing condition of a closed chain, in the form of `List.isChain_append`. -/
theorem close_of_getLast_head {α : Type*} {R : α → α → Prop} {l : List α} (hne : l ≠ [])
    (h : R (l.getLast hne) (l.head hne)) : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b := by
  intro a ha b hb
  rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some_inj] at ha
  rw [List.head?_eq_some_head hne, Option.mem_def, Option.some_inj] at hb
  rw [← ha, ← hb]
  exact h

section Regions

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
  {faces : Finset X.toCombMap.Face}

/-- **The left stretch of a region**: from the last target dart, along the left side, to the first
reversed source dart.  It crosses the base point of the boundary cycle, so the last step is the
closing step of the cycle. -/
theorem isChain_leftStretch (H : ContiguityGeometry D eps X faces) {s t : List X.toCombMap.Dart}
    (hs : s = H.sourceArc.reverseDarts) (ht : t = targetBoundaryDarts X H.target H.targetArc)
    (hsne : s ≠ []) (htne : t ≠ []) :
    (t.getLast htne :: H.leftSide ++ [s.head hsne]).IsChain
      (Surgery.MapCollapse.BoundaryWalk X.toCombMap faces) := by
  have hchain := H.boundary.cycle_chain
  have hclose := close_of_getLast_head H.boundary.cycle_nonempty H.boundary.cycle_closes
  rw [H.boundary_decomposition, ← hs, ← ht] at hchain hclose
  have heq : s ++ H.rightSide ++ t ++ H.leftSide =
      (s ++ H.rightSide ++ t.dropLast) ++ (t.getLast htne :: H.leftSide) := by
    conv_lhs => rw [← List.dropLast_append_getLast htne]
    simp only [List.append_assoc, List.singleton_append]
  rw [heq] at hchain hclose
  have hL : (t.getLast htne :: H.leftSide).IsChain (BoundaryStep X faces) :=
    (List.isChain_append.mp hchain).2.1
  refine (List.isChain_append.mpr ⟨hL, List.isChain_singleton _, fun a ha b hb => ?_⟩).imp
    fun _ _ h => boundaryWalk_of_boundaryStep h
  obtain rfl : s.head hsne = b := by simpa using hb
  exact hclose a (List.mem_getLast?_append_of_mem_getLast? ha) _
    (List.mem_head?_append_of_mem_head? (List.mem_head?_append_of_mem_head?
      (List.mem_head?_append_of_mem_head? (Option.mem_def.mpr (List.head?_eq_some_head hsne)))))

/-- **The right stretch of a region**: from the last reversed source dart, along the right side,
to the first target dart. -/
theorem isChain_rightStretch (H : ContiguityGeometry D eps X faces) {s t : List X.toCombMap.Dart}
    (hs : s = H.sourceArc.reverseDarts) (ht : t = targetBoundaryDarts X H.target H.targetArc)
    (hsne : s ≠ []) (htne : t ≠ []) :
    (s.getLast hsne :: H.rightSide ++ [t.head htne]).IsChain
      (Surgery.MapCollapse.BoundaryWalk X.toCombMap faces) := by
  have hchain := H.boundary.cycle_chain
  rw [H.boundary_decomposition, ← hs, ← ht] at hchain
  have h := isChain_middle hsne htne (List.isChain_append.mp hchain).1
  exact h.imp fun _ _ h => boundaryWalk_of_boundaryStep h

end Regions

section Cell

variable {M : CombMap.{u}}

/-- **A closed face walk, as a closing condition.** -/
theorem close_of_faceBoundary {f : M.Face} (B : FaceBoundary M f) :
    ∀ a ∈ B.darts.getLast?, ∀ b ∈ B.darts.head?, M.facePerm a = b :=
  close_of_getLast_head B.nonempty B.closes

/-- **The cell stretch**: an arc of a face that reads `X`, then `Gap`, then `Y`, with `X` and `Y`
nonempty, gives a face walk from the last dart of `X` through `Gap` to the first dart of `Y`. -/
theorem isChain_cellStretch {f : M.Face} (B : FaceBoundary M f) {T : CyclicArc B.darts}
    {Xd Gap Yd : List M.Dart} (hT : T.darts = Xd ++ Gap ++ Yd) (hX : Xd ≠ []) (hY : Yd ≠ []) :
    (Xd.getLast hX :: Gap ++ [Yd.head hY]).IsChain fun a b => M.facePerm a = b := by
  have h := CyclicArc.isChain_darts T B.chain (close_of_faceBoundary B)
  rw [hT] at h
  exact isChain_middle hX hY h

/-- **The oriented outer boundary is a backward face walk** of the exterior face: consecutive
darts `d, e` have `facePerm (alpha e) = alpha d`. -/
theorem isChain_reverse_map_alpha_face {f : M.Face} (B : FaceBoundary M f) :
    (B.darts.reverse.map M.alpha).IsChain fun d e => M.facePerm (M.alpha e) = M.alpha d := by
  refine (List.isChain_map M.alpha).2 (List.isChain_reverse.2 ?_)
  refine B.chain.imp fun a b h => ?_
  show M.facePerm (M.alpha (M.alpha a)) = M.alpha (M.alpha b)
  rw [M.alpha_involutive a, M.alpha_involutive b]
  exact h

/-- **A window of a chain is a chain.** -/
theorem isChain_window {α : Type*} {R : α → α → Prop} {L : List α} (h : L.IsChain R)
    (p n : ℕ) : ((L.drop p).take n).IsChain R := by
  rw [← List.take_append_drop p L] at h
  have h₁ := (List.isChain_append.mp h).2.1
  rw [← List.take_append_drop n (L.drop p)] at h₁
  exact (List.isChain_append.mp h₁).1

/-- **A backward stretch, read backwards on reversed darts, is a face walk**, and it reads the
first dart of `B` reversed, then `G` read backwards, then the last dart of `A` reversed. -/
theorem isChain_outerStretch {A G B : List M.Dart} (hA : A ≠ []) (hB : B ≠ [])
    (h : (A ++ G ++ B).IsChain fun d e => M.facePerm (M.alpha e) = M.alpha d) :
    (M.alpha (B.head hB) :: G.reverse.map M.alpha ++ [M.alpha (A.getLast hA)]).IsChain
      fun a b => M.facePerm a = b := by
  have hm := isChain_middle hA hB h
  have hr : ((A.getLast hA :: G ++ [B.head hB]).reverse.map M.alpha).IsChain
      fun a b => M.facePerm a = b :=
    (List.isChain_map M.alpha).2 (List.isChain_reverse.2 (hm.imp fun _ _ h => h))
  have heq : ((A.getLast hA :: G ++ [B.head hB]).reverse.map M.alpha) =
      M.alpha (B.head hB) :: G.reverse.map M.alpha ++ [M.alpha (A.getLast hA)] := by
    simp [List.reverse_append]
  rw [heq] at hr
  exact hr

end Cell

/-! ## The stretches, with the ends named by decompositions -/

/-- **The middle of a chain, by decomposition**: `a`, then `G`, then `b`, out of
`A ++ [a] ++ G ++ b :: B`. -/
theorem isChain_middle' {α : Type*} {R : α → α → Prop} {A G B : List α} {a b : α}
    (h : (A ++ [a] ++ G ++ (b :: B)).IsChain R) : (a :: G ++ [b]).IsChain R := by
  have heq : A ++ [a] ++ G ++ (b :: B) = A ++ ((a :: G ++ [b]) ++ B) := by simp
  rw [heq] at h
  exact (List.isChain_append.mp (List.isChain_append.mp h).2.1).1

section Regions'

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
  {faces : Finset X.toCombMap.Face}

/-- **The left stretch, by decomposition**: the reversed source darts start with `b`, the target
darts end with `a`; then `a`, the left side, `b` is a chain of boundary walks. -/
theorem isChain_leftStretch' (H : ContiguityGeometry D eps X faces) {s t : List X.toCombMap.Dart}
    {a b : X.toCombMap.Dart} (hs : H.sourceArc.reverseDarts = b :: s)
    (ht : targetBoundaryDarts X H.target H.targetArc = t ++ [a]) :
    (a :: H.leftSide ++ [b]).IsChain (Surgery.MapCollapse.BoundaryWalk X.toCombMap faces) := by
  have hchain := H.boundary.cycle_chain
  have hclose := close_of_getLast_head H.boundary.cycle_nonempty H.boundary.cycle_closes
  rw [H.boundary_decomposition, hs, ht] at hchain hclose
  have heq : (b :: s) ++ H.rightSide ++ (t ++ [a]) ++ H.leftSide =
      ((b :: s) ++ H.rightSide ++ t) ++ (a :: H.leftSide) := by simp
  rw [heq] at hchain hclose
  have hL : (a :: H.leftSide).IsChain (BoundaryStep X faces) := (List.isChain_append.mp hchain).2.1
  refine (List.isChain_append.mpr ⟨hL, List.isChain_singleton _, fun p hp q hq => ?_⟩).imp
    fun _ _ h => boundaryWalk_of_boundaryStep h
  obtain rfl : b = q := by simpa using hq
  exact hclose p (List.mem_getLast?_append_of_mem_getLast? hp) q (by simp)

/-- **The right stretch, by decomposition**: the reversed source darts end with `a`, the target
darts start with `b`; then `a`, the right side, `b` is a chain of boundary walks. -/
theorem isChain_rightStretch' (H : ContiguityGeometry D eps X faces) {s t : List X.toCombMap.Dart}
    {a b : X.toCombMap.Dart} (hs : H.sourceArc.reverseDarts = s ++ [a])
    (ht : targetBoundaryDarts X H.target H.targetArc = b :: t) :
    (a :: H.rightSide ++ [b]).IsChain (Surgery.MapCollapse.BoundaryWalk X.toCombMap faces) := by
  have hchain := H.boundary.cycle_chain
  rw [H.boundary_decomposition, hs, ht] at hchain
  have h := isChain_middle' (List.isChain_append.mp hchain).1
  exact h.imp fun _ _ h => boundaryWalk_of_boundaryStep h

end Regions'

section Cell'

variable {M : CombMap.{u}}

/-- **The cell stretch, by decomposition.** -/
theorem isChain_cellStretch' {f : M.Face} (B : FaceBoundary M f) {T : CyclicArc B.darts}
    {Xd Gap Yd : List M.Dart} {p q : M.Dart} (hT : T.darts = Xd ++ [p] ++ Gap ++ (q :: Yd)) :
    (p :: Gap ++ [q]).IsChain fun a b => M.facePerm a = b := by
  have h := CyclicArc.isChain_darts T B.chain (close_of_faceBoundary B)
  rw [hT] at h
  exact isChain_middle' h

/-- **The outer stretch, by decomposition**: a backward chain `A ++ [a] ++ G ++ b :: B` gives the
face walk `alpha b`, `G` read backwards, `alpha a`. -/
theorem isChain_outerStretch' {A G B : List M.Dart} {a b : M.Dart}
    (h : (A ++ [a] ++ G ++ (b :: B)).IsChain fun d e => M.facePerm (M.alpha e) = M.alpha d) :
    (M.alpha b :: G.reverse.map M.alpha ++ [M.alpha a]).IsChain fun a b => M.facePerm a = b := by
  have hm := isChain_middle' h
  have hr : ((a :: G ++ [b]).reverse.map M.alpha).IsChain fun a b => M.facePerm a = b :=
    (List.isChain_map M.alpha).2 (List.isChain_reverse.2 (hm.imp fun _ _ h => h))
  have heq : ((a :: G ++ [b]).reverse.map M.alpha) =
      M.alpha b :: G.reverse.map M.alpha ++ [M.alpha a] := by
    simp [List.reverse_append]
  rw [heq] at hr
  exact hr

end Cell'

end ExclusiveStretch

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_middle
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_leftStretch
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_rightStretch
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_cellStretch
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_reverse_map_alpha_face
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_window
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_outerStretch
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_leftStretch'
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_rightStretch'
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_cellStretch'
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_outerStretch'
