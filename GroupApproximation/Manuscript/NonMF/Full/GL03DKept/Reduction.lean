import GroupApproximation.Manuscript.NonMF.Full.GL03DKept.Core
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept sub-walk statement from its core, and back

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

* `gl03dKept_keptSubwalk_of_core`: `gl03dKept_KeptSubwalkCoreStatement` gives
  `Full.GL03D.KeptSubwalkStatement`.  The noncrossing walk comes from
  `gl03dKept_isNoncrossing_filter`.  A kept dart of `t_2` has the exterior across it, a kept dart
  of `t_1⁻¹` the source cell, and both are then off the side by Jordan separation.  A kept dart on
  a relator cell puts that cell on the side.
* `gl03dKept_core_of_keptSubwalk`: the converse, so the core is exactly as true as the original.
-/

namespace GroupApproximation.Full.GL03DKept

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **The kept sub-walk statement from its core** (Osin Lemma 9.7(b), for `thm:hull`). -/
theorem gl03dKept_keptSubwalk_of_core (h : gl03dKept_KeptSubwalkCoreStatement.{u, w, v}) :
    GL03D.KeptSubwalkStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  obtain ⟨q, hne, hchain, hcloses, hturn, hproper, hout, hsource, hkept, hsrcBlock, htgtBlock⟩ :=
    h D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  have hw : IsNoncrossingClosedWalk X.toCombMap (K.boundary.cycle.filter q) :=
    gl03dKept_isNoncrossing_filter K.boundary q hne hchain (hcloses hne) hturn
  refine ⟨q, hw, hproper, ?_, ?_, ?_, hsrcBlock, htgtBlock⟩
  · rcases hout with hout | ⟨d, hd, hqd⟩
    · exact hout
    · have hdB : d ∈ K.boundary.cycle.filter q :=
        List.mem_filter.mpr ⟨GL05b.mem_cycle_of_mem_targetArc K hd, hqd⟩
      rw [← GL05b.faceOf_alpha_of_mem_targetArc K hd]
      exact gl03dKept_faceOf_alpha_not_mem_sideFaces hw X.planar hdB
  · rcases hsource with hsource | ⟨d, hd, hqd⟩
    · exact hsource
    · have hdB : d ∈ K.boundary.cycle.filter q :=
        List.mem_filter.mpr ⟨GL05b.mem_cycle_of_mem_invSourceArc K hd, hqd⟩
      rw [← GL05b.faceOf_alpha_of_mem_invSourceArc K hd]
      exact gl03dKept_faceOf_alpha_not_mem_sideFaces hw X.planar hdB
  · rcases hkept with hkept | ⟨d, hd, hqd, kept, hface⟩
    · exact hkept
    · have hdB : d ∈ K.boundary.cycle.filter q := List.mem_filter.mpr ⟨hd, hqd⟩
      refine ⟨kept, ?_⟩
      rw [← hface]
      exact gl03dKept_faceOf_mem_sideFaces hdB

/-- **The core from the kept sub-walk statement**: the core is no stronger than the original. -/
theorem gl03dKept_core_of_keptSubwalk (h : GL03D.KeptSubwalkStatement.{u, w, v}) :
    gl03dKept_KeptSubwalkCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  obtain ⟨q, hw, hproper, hout, hsource, hkept, hsrcBlock, htgtBlock⟩ :=
    h D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  exact ⟨q, hw.ne_nil, hw.chain, fun _ => hw.closes, hw.turn_mem, hproper, Or.inl hout,
    Or.inl hsource, Or.inl hkept, hsrcBlock, htgtBlock⟩

end GroupApproximation.Full.GL03DKept

#audit_axioms GroupApproximation.Full.GL03DKept.gl03dKept_keptSubwalk_of_core
#audit_axioms GroupApproximation.Full.GL03DKept.gl03dKept_core_of_keptSubwalk
