import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-57: two list facts for the descent induction

Lane gl-p07-57.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepPinchArc_mem_pre_of_before`: in a word without duplicates, a letter placed before a
  letter of a prefix lies in that prefix.
* `witnessStepPinchArc_split_after`: a letter `x` of `w` off a prefix `pre`, and a letter `y` of
  `pre`, give `w = p ++ y :: (mid ++ x :: post)` with `p` strictly shorter than `pre`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

/-- **Before a prefix letter means in the prefix.**  If `w` has no duplicates, `w = pre ++ r`,
`x` comes before `y` in `w`, and `y ∈ pre`, then `x ∈ pre`. -/
theorem witnessStepPinchArc_mem_pre_of_before {β : Type*} {w pre r u v z : List β} {x y : β}
    (hnd : w.Nodup) (hw : w = pre ++ r) (hw' : w = u ++ x :: (v ++ y :: z)) (hy : y ∈ pre) :
    x ∈ pre := by
  obtain ⟨p₁, p₂, hp⟩ := List.append_of_mem hy
  have h1 : w = p₁ ++ y :: (p₂ ++ r) := by
    rw [hw, hp]
    simp
  have h2 : w = (u ++ x :: v) ++ y :: z := by
    rw [hw']
    simp
  have hnd' : (p₁ ++ y :: (p₂ ++ r)).Nodup := by
    rw [← h1]
    exact hnd
  obtain ⟨hpu, -⟩ := WitnessCurveSublistList.append_cons_inj_of_nodup hnd' (h1.symm.trans h2)
  rw [hp, hpu]
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchArc_mem_pre_of_before

/-- **Split after a prefix letter.**  If `w = pre ++ r`, `y ∈ pre`, and `x ∈ w` is off `pre`, then
`w = p ++ y :: (mid ++ x :: post)` for some `p` strictly shorter than `pre`. -/
theorem witnessStepPinchArc_split_after {β : Type*} {w pre r : List β} {x y : β}
    (hw : w = pre ++ r) (hy : y ∈ pre) (hx : x ∈ w) (hxp : x ∉ pre) :
    ∃ p mid post : List β, w = p ++ y :: (mid ++ x :: post) ∧ p.length < pre.length := by
  obtain ⟨p₁, p₂, hp⟩ := List.append_of_mem hy
  have hxw : x ∈ pre ++ r := by
    rw [← hw]
    exact hx
  have hxr : x ∈ p₂ ++ r := by
    rcases List.mem_append.mp hxw with h | h
    · exact absurd h hxp
    · exact List.mem_append_right _ h
  obtain ⟨mid, post, hm⟩ := List.append_of_mem hxr
  refine ⟨p₁, mid, post, ?_, ?_⟩
  · rw [hw, hp, ← hm]
    simp
  · rw [hp, List.length_append, List.length_cons]
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchArc_split_after

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
