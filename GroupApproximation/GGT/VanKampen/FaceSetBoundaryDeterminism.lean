import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation

/-!
# The boundary walk of a face set is deterministic

`Estimating.Embedded.BoundaryStep` is stated as a reflexive transitive closure
of `InternalBoundaryMove`, not as a successor function, so a priori a boundary
dart could have several successors.  It does not: `InternalBoundaryMove` is a
function of its source (the next dart is `facePerm (alpha d)`), and a boundary
dart admits no internal move at all, because an internal move requires the
face across `alpha` to be selected while a boundary dart requires it not to
be.  So each `BoundaryStep` reaches the unique terminal point of a
deterministic reachability relation.

Two consequences are proved.  First, `boundaryStep_right_unique`: this is the
right-uniqueness fact the peel producer needs, and it is derived inside
`VanKampen` from the permutation map, so no field has to be added to est's
`FaceSetBoundary`.  Second, `FaceSetBoundary.exists_cycle_eq_rotate`: the
cyclic list stored by a `FaceSetBoundary` is determined by its face set up to
rotation.  Together with the rotation algebra in `FaceSetMoveAlgebra` this
makes the base dart of a boundary record irrelevant.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

/-! ## Generic determinism lemmas -/

/-- In a right-unique relation two reachable terminal points coincide. -/
private theorem eq_of_reflTransGen_of_terminal
    {α : Type*} {r : α → α → Prop} (huniq : Relator.RightUnique r)
    {a b c : α}
    (hbterm : ∀ x : α, ¬ r b x) (hcterm : ∀ x : α, ¬ r c x)
    (hb : Relation.ReflTransGen r a b) (hc : Relation.ReflTransGen r a c) :
    b = c := by
  rcases Relation.ReflTransGen.total_of_right_unique huniq hb hc with h | h
  · rcases Relation.ReflTransGen.cases_head h with heq | ⟨_, hstep, _⟩
    · exact heq
    · exact absurd hstep (hbterm _)
  · rcases Relation.ReflTransGen.cases_head h with heq | ⟨_, hstep, _⟩
    · exact heq.symm
    · exact absurd hstep (hcterm _)

/-- Two chains for a right-unique relation which start at the same element
agree at every common index. -/
private theorem getElem_eq_of_isChain_right_unique
    {α : Type*} {R : α → α → Prop}
    (huniq : ∀ x y z : α, R x y → R x z → y = z)
    {first second : List α}
    (hfirst : first.IsChain R) (hsecond : second.IsChain R)
    (hhead : ∀ (p : 0 < first.length) (q : 0 < second.length),
      first[0] = second[0]) :
    ∀ (n : ℕ) (p : n < first.length) (q : n < second.length),
      first[n] = second[n] := by
  intro n
  induction n with
  | zero =>
      intro p q
      exact hhead p q
  | succ n ih =>
      intro p q
      have hp : n < first.length := by omega
      have hq : n < second.length := by omega
      have hprev : first[n] = second[n] := ih hp hq
      have hstepFirst : R first[n] first[n + 1] :=
        List.isChain_iff_getElem.mp hfirst n p
      have hstepSecond : R second[n] second[n + 1] :=
        List.isChain_iff_getElem.mp hsecond n q
      rw [hprev] at hstepFirst
      exact huniq second[n] first[n + 1] second[n + 1] hstepFirst hstepSecond

/-- Two chains of the same length for a right-unique relation with the same
first element are equal. -/
private theorem eq_of_isChain_right_unique
    {α : Type*} {R : α → α → Prop}
    (huniq : ∀ x y z : α, R x y → R x z → y = z)
    {first second : List α}
    (hfirst : first.IsChain R) (hsecond : second.IsChain R)
    (hlen : first.length = second.length)
    (hhead : ∀ (p : 0 < first.length) (q : 0 < second.length),
      first[0] = second[0]) :
    first = second :=
  List.ext_getElem hlen
    (getElem_eq_of_isChain_right_unique huniq hfirst hsecond hhead)

/-- Rotating a list to the position of a distinguished element puts that
element at the head. -/
private theorem rotate_append_cons
    {α : Type*} (pre : List α) (a : α) (suf : List α) :
    (pre ++ a :: suf).rotate pre.length = a :: (suf ++ pre) := by
  rw [List.rotate_append_length_eq, List.cons_append]

/-- Reading the head of a list presented as a cons. -/
private theorem head_eq_of_eq_cons
    {α : Type*} {l : List α} {a : α} {t : List α} (h : l = a :: t)
    (hne : l ≠ []) : l.head hne = a := by
  subst h
  rfl

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-! ## Determinism of the boundary walk -/

/-- Crossing an internal edge determines the next dart: it is the face
rotation of the reversed dart. -/
theorem internalBoundaryMove_rightUnique
    (faces : Finset Delta.toCombMap.Face) :
    Relator.RightUnique (InternalBoundaryMove Delta faces) :=
  fun _ _ _ hfirst hsecond => hfirst.2.2.trans hsecond.2.2.symm

/-- A boundary dart admits no internal move: an internal move needs the face
across `alpha` to be selected, and a boundary dart needs it unselected. -/
theorem not_internalBoundaryMove_of_isBoundaryDart
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hd : IsBoundaryDart Delta faces d) :
    ¬ InternalBoundaryMove Delta faces d e :=
  fun hmove => hd.2 hmove.2.1

/-- The boundary walk of a face set is a function: a boundary dart has at
most one `BoundaryStep` successor. -/
theorem boundaryStep_right_unique
    {faces : Finset Delta.toCombMap.Face}
    {d first second : Delta.toCombMap.Dart}
    (hfirst : BoundaryStep Delta faces d first)
    (hsecond : BoundaryStep Delta faces d second) :
    first = second :=
  eq_of_reflTransGen_of_terminal (internalBoundaryMove_rightUnique faces)
    (fun _ => not_internalBoundaryMove_of_isBoundaryDart hfirst.2.1)
    (fun _ => not_internalBoundaryMove_of_isBoundaryDart hsecond.2.1)
    hfirst.2.2 hsecond.2.2

/-- `BoundaryStep` packaged as a right-unique relation. -/
theorem rightUnique_boundaryStep
    (faces : Finset Delta.toCombMap.Face) :
    Relator.RightUnique (BoundaryStep Delta faces) :=
  fun _ _ _ hfirst hsecond => boundaryStep_right_unique hfirst hsecond

/-! ## The boundary cycle is determined up to rotation -/

/-- Two boundary records for the same face set enumerate the same darts. -/
theorem FaceSetBoundary.cycle_perm
    {faces : Finset Delta.toCombMap.Face}
    (first second : FaceSetBoundary Delta faces) :
    List.Perm first.cycle second.cycle := by
  rw [List.perm_ext_iff_of_nodup first.cycle_nodup second.cycle_nodup]
  intro d
  rw [first.cycle_mem_iff d, second.cycle_mem_iff d]

/-- Two boundary records for the same face set based at the same dart have
the same cycle. -/
theorem FaceSetBoundary.cycle_eq_of_head_eq
    {faces : Finset Delta.toCombMap.Face}
    (first second : FaceSetBoundary Delta faces)
    (hhead : first.cycle.head first.cycle_nonempty =
      second.cycle.head second.cycle_nonempty) :
    first.cycle = second.cycle := by
  refine eq_of_isChain_right_unique (R := BoundaryStep Delta faces)
    (fun _ _ _ hone htwo => boundaryStep_right_unique hone htwo)
    first.cycle_chain second.cycle_chain
    (FaceSetBoundary.cycle_perm first second).length_eq ?_
  intro p q
  have hone := List.head_eq_getElem_zero first.cycle_nonempty
  have htwo := List.head_eq_getElem_zero second.cycle_nonempty
  rw [hone, htwo] at hhead
  exact hhead

/-- The cyclic list stored by a boundary record is determined by its face set
up to rotation. -/
theorem FaceSetBoundary.exists_cycle_eq_rotate
    {faces : Finset Delta.toCombMap.Face}
    (first second : FaceSetBoundary Delta faces) :
    ∃ k : ℕ, first.cycle = second.cycle.rotate k := by
  have hd : IsBoundaryDart Delta faces
      (first.cycle.head first.cycle_nonempty) :=
    (first.cycle_mem_iff _).1 (List.head_mem first.cycle_nonempty)
  have hmem : first.cycle.head first.cycle_nonempty ∈ second.cycle :=
    (second.cycle_mem_iff _).2 hd
  obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem hmem
  refine ⟨pre.length, ?_⟩
  have hrot : (second.rotate pre.length).cycle =
      first.cycle.head first.cycle_nonempty :: (suf ++ pre) := by
    rw [FaceSetBoundary.rotate_cycle, hsplit, rotate_append_cons]
  have hhead := head_eq_of_eq_cons hrot
    (second.rotate pre.length).cycle_nonempty
  have hcycle := FaceSetBoundary.cycle_eq_of_head_eq first
    (second.rotate pre.length) hhead.symm
  exact hcycle.trans (FaceSetBoundary.rotate_cycle second pre.length)

end Embedded
end VanKampen
end GGT
end GroupApproximation
