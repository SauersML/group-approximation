import GroupApproximation.Manuscript.NonMF.Full.GL03DKept.Core
import GroupApproximation.Meta.AxiomGuard

/-!
# Pinch segments of a boundary cycle are noncrossing walks

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Infrastructure for `thm:hull` in `non_mf_groups_exist.tex` (around
line 2121); certifies no printed sentence on its own.

The core statement `GL03DKept.gl03dKept_KeptSubwalkCoreStatement` asks for a filter
`B = cycle.filter q` of the pocket boundary cycle that is a nonempty closed walk in cycle order
with the noncrossing turning condition.  This module shows that the turning condition, and the
chain condition, come for free for a *pinch segment*: a contiguous stretch `B <:+: cycle` of the
closed walk `cycle`, ending where it starts, whose darts start at pairwise distinct vertices.
Such a `B` is a simple closed walk, hence noncrossing
(`IsSimpleClosedWalk.isNoncrossingClosedWalk`).

A pinched pocket always has a pinch segment.  Take positions `i < j` of the cycle whose darts
start at the same vertex, with `j - i` least; the stretch `[i, j)` has distinct start vertices.
That existence argument is not formalised here, because the `q` of the core must also satisfy
the side and end-block conditions.

* `gl03dKeptProof_CoreWalk`: the walk part of the core (nonempty, chain, closing, turning).
* `gl03dKeptProof_PinchSegment`: a nonempty closing infix with distinct start vertices.
* `gl03dKeptProof_coreWalk_of_pinch`: for a filter of a boundary cycle that is a closed walk, a
  pinch segment satisfies the walk part.
* `gl03dKeptProof_filter_eq_nil`, `gl03dKeptProof_isEndBlock_of_forall_false`: a predicate
  false on a whole list filters it to the empty prefix.
-/

namespace GroupApproximation.Full.GL03DKeptProof

universe v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **The walk part of the kept sub-walk core**: `B` is a nonempty closed walk with the
noncrossing turning condition.  These are the first four conjuncts of
`GL03DKept.gl03dKept_KeptSubwalkCoreStatement`. -/
def gl03dKeptProof_CoreWalk (M : CombMap.{v}) (B : List M.Dart) : Prop :=
  B ≠ [] ∧ B.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) ∧
    (∀ hne : B ≠ [], M.vertexOf (M.alpha (B.getLast hne)) = M.vertexOf (B.head hne)) ∧
    (∀ d ∈ B, ∀ m : ℕ, 0 < m → walkKeep M B ((M.sigma ^ m) (M.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep M B ((M.sigma ^ k) (M.alpha d))) →
      (M.sigma ^ m) (M.alpha d) ∈ B)

/-- **A pinch segment** of a closed walk `c`: a nonempty contiguous stretch `B` of `c` that ends
where it starts and whose darts start at pairwise distinct vertices. -/
def gl03dKeptProof_PinchSegment (M : CombMap.{v}) (c B : List M.Dart) : Prop :=
  ∃ hne : B ≠ [], B <:+: c ∧
    M.vertexOf (M.alpha (B.getLast hne)) = M.vertexOf (B.head hne) ∧
    (B.map M.vertexOf).Nodup

/-- **A pinch segment of a boundary cycle is a noncrossing closed walk** (for `thm:hull`).  The
chain comes from the cycle, one-way edges from the boundary cycle, and the turning condition from
`IsSimpleClosedWalk.isNoncrossingClosedWalk`. -/
theorem gl03dKeptProof_coreWalk_of_pinch {M : CombMap.{v}} {faces : Finset M.Face}
    (b : Surgery.MapCollapse.BoundaryCycle M faces) (q : M.Dart → Bool)
    (hchain : b.cycle.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hp : gl03dKeptProof_PinchSegment M b.cycle (b.cycle.filter q)) :
    gl03dKeptProof_CoreWalk M (b.cycle.filter q) := by
  obtain ⟨hne, hinf, hcl, hvert⟩ := hp
  have hs : GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk M (b.cycle.filter q) :=
    { ne_nil := hne
      chain := hchain.infix hinf
      closes := hcl
      vertex_nodup := hvert
      alpha_not_mem := by
        intro d hd ha
        have hb : M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces :=
          (b.cycle_mem_iff d).mp (List.mem_filter.mp hd).1
        have hb' : M.faceOf (M.alpha d) ∈ faces ∧ M.faceOf (M.alpha (M.alpha d)) ∉ faces :=
          (b.cycle_mem_iff (M.alpha d)).mp (List.mem_filter.mp ha).1
        exact hb.2 hb'.1 }
  have hn : IsNoncrossingClosedWalk M (b.cycle.filter q) := hs.isNoncrossingClosedWalk
  exact ⟨hne, hn.chain, fun _ => hcl, hn.turn_mem⟩

/-- A predicate false on a whole list filters it to the empty list. -/
theorem gl03dKeptProof_filter_eq_nil {α : Type*} {p : α → Bool} {l : List α}
    (h : ∀ a ∈ l, p a = false) : l.filter p = [] :=
  List.filter_eq_nil_iff.mpr fun a ha hp => by
    rw [h a ha] at hp
    exact absurd hp (by decide)

/-- A predicate false on a whole list gives the empty prefix, an end block. -/
theorem gl03dKeptProof_isEndBlock_of_forall_false {α : Type*} {p : α → Bool} {l : List α}
    (h : ∀ a ∈ l, p a = false) : GL05b.IsEndBlock p l :=
  ⟨0, Or.inl (by rw [gl03dKeptProof_filter_eq_nil h, List.take_zero])⟩

end GroupApproximation.Full.GL03DKeptProof

#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_CoreWalk
#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_PinchSegment
#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_coreWalk_of_pinch
#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_filter_eq_nil
#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_isEndBlock_of_forall_false
