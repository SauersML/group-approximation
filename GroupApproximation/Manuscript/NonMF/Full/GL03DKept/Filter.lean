import GroupApproximation.Manuscript.NonMF.Full.GL03D.KeptWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Filtered boundary cycles: the generic half of a kept sub-walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Infrastructure for `thm:hull` in `non_mf_groups_exist.tex` (around
line 2121); certifies no printed sentence on its own.

`Full.GL03D.KeptSubwalkStatement` asks for a choice `q` of darts of a pocket boundary cycle whose
filter `B = cycle.filter q` is a noncrossing closed walk, with side conditions.  Part of that is
automatic for any filter of a boundary cycle, and this module proves it:

* `gl03dKept_isNoncrossing_filter`: `B` is duplicate-free and uses no edge in both directions,
  because the cycle is a boundary cycle.  Only nonemptiness, the chain, closing and the turning
  condition are left to check.
* `gl03dKept_faceOf_mem_sideFaces`: a dart of a walk has its face on the side of the walk.
* `gl03dKept_faceOf_alpha_not_mem_sideFaces`: across a dart of a noncrossing walk lies a face
  off its side (the Jordan separation `isBoundaryDart_sideFaces_iff`).
-/

namespace GroupApproximation.Full.GL03DKept

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **A filter of a boundary cycle is noncrossing once it walks and turns correctly** (for
`thm:hull`).  Duplicate-freeness and the absence of edges used in both directions come from the
boundary cycle. -/
theorem gl03dKept_isNoncrossing_filter {M : CombMap.{v}} {faces : Finset M.Face}
    (b : Surgery.MapCollapse.BoundaryCycle M faces) (q : M.Dart → Bool)
    (hne : b.cycle.filter q ≠ [])
    (hchain : (b.cycle.filter q).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : M.vertexOf (M.alpha ((b.cycle.filter q).getLast hne)) =
      M.vertexOf ((b.cycle.filter q).head hne))
    (hturn : ∀ d ∈ b.cycle.filter q, ∀ m : ℕ, 0 < m →
      walkKeep M (b.cycle.filter q) ((M.sigma ^ m) (M.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep M (b.cycle.filter q) ((M.sigma ^ k) (M.alpha d))) →
      (M.sigma ^ m) (M.alpha d) ∈ b.cycle.filter q) :
    IsNoncrossingClosedWalk M (b.cycle.filter q) where
  ne_nil := hne
  nodup := List.Nodup.filter q b.cycle_nodup
  chain := hchain
  closes := hcloses
  alpha_not_mem := by
    intro d hd ha
    have hb : M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces :=
      (b.cycle_mem_iff d).mp (List.mem_filter.mp hd).1
    have hb' : M.faceOf (M.alpha d) ∈ faces ∧ M.faceOf (M.alpha (M.alpha d)) ∉ faces :=
      (b.cycle_mem_iff (M.alpha d)).mp (List.mem_filter.mp ha).1
    exact hb.2 hb'.1
  turn_mem := hturn

/-- A dart of a walk has its face on the side of the walk. -/
theorem gl03dKept_faceOf_mem_sideFaces {M : CombMap.{v}} {B : List M.Dart} {d : M.Dart}
    (hd : d ∈ B) : M.faceOf d ∈ sideFaces M B :=
  (mem_sideFaces_iff M B d).mpr ⟨d, hd, Relation.EqvGen.refl _⟩

/-- Across a dart of a noncrossing closed walk lies a face off its side. -/
theorem gl03dKept_faceOf_alpha_not_mem_sideFaces {M : CombMap.{v}} {B : List M.Dart}
    (hw : IsNoncrossingClosedWalk M B) (hM : M.IsPlanar) {d : M.Dart} (hd : d ∈ B) :
    M.faceOf (M.alpha d) ∉ sideFaces M B := by
  have h : M.faceOf d ∈ sideFaces M B ∧ M.faceOf (M.alpha d) ∉ sideFaces M B :=
    (hw.isBoundaryDart_sideFaces_iff hM d).mpr hd
  exact h.2

end GroupApproximation.Full.GL03DKept

#audit_axioms GroupApproximation.Full.GL03DKept.gl03dKept_isNoncrossing_filter
#audit_axioms GroupApproximation.Full.GL03DKept.gl03dKept_faceOf_mem_sideFaces
#audit_axioms GroupApproximation.Full.GL03DKept.gl03dKept_faceOf_alpha_not_mem_sideFaces
