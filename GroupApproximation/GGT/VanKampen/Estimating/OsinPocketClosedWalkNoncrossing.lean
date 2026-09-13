import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket face set in walk order is a noncrossing closed walk

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

A boundary cycle lists the darts whose face is selected and whose reversal's face is not.  Rotate
around a vertex from the reversal `alpha d` of a listed dart `d`.  The corner right after
`alpha d` lies in the face of `d`, which is selected.  A dart met there that is not on an edge of
the listing has both of its faces selected, so the next corner is selected too.  So the first dart
met on an edge of the listing has a selected face: it is a listed dart, not the reversal of one.
This is the turning condition of `IsNoncrossingClosedWalk`, for every listing of every face set.
So a boundary cycle in walk order, and in particular a pocket face set in walk order
(`PocketFaceSet.ClosedWalk`), is a noncrossing closed walk.  The turning condition does not choose
how the walk pairs its darts at a vertex it passes more than once.

* `BoundaryCycle.faceOf_sigma_pow_alpha_mem`: rotating from `alpha d` past darts off the edges of
  the listing stays in selected faces.
* `BoundaryCycle.turn_mem_cycle`: the turning condition for a boundary cycle.
* `BoundaryCycle.isNoncrossingClosedWalk`: a boundary cycle in walk order is a noncrossing closed
  walk.
* `PocketFaceSet.ClosedWalk.isNoncrossingClosedWalk`: a pocket face set in walk order is a
  noncrossing closed walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Equiv SimpleClosedWalkSides

namespace Surgery.MapCollapse.BoundaryCycle

variable {M : CombMap.{v}} {faces : Finset M.Face}

/-- **Rotating from a reversed boundary dart stays in selected faces.**  As long as no earlier
dart is on an edge of the listing, the `k`-th dart met rotating from `alpha d` has a selected
face. -/
theorem faceOf_sigma_pow_alpha_mem (B : BoundaryCycle M faces) {d : M.Dart} (hd : d ∈ B.cycle) :
    ∀ k : ℕ, 0 < k →
      (∀ j, 0 < j → j < k → ¬ walkKeep M B.cycle ((M.sigma ^ j) (M.alpha d))) →
        M.faceOf ((M.sigma ^ k) (M.alpha d)) ∈ faces := by
  intro k
  induction k with
  | zero => intro hk; exact absurd hk (Nat.lt_irrefl 0)
  | succ k ih =>
      intro _ havoid
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · have hb : M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces :=
          (B.cycle_mem_iff d).mp hd
        have hface : M.faceOf ((M.sigma ^ (0 + 1)) (M.alpha d)) = M.faceOf d := by
          rw [zero_add, pow_one]
          exact M.faceOf_facePerm d
        rw [hface]
        exact hb.1
      · have hy : M.faceOf ((M.sigma ^ k) (M.alpha d)) ∈ faces :=
          ih hpos fun j hj hjk => havoid j hj (Nat.lt_succ_of_lt hjk)
        have hoff : ¬ walkKeep M B.cycle ((M.sigma ^ k) (M.alpha d)) :=
          havoid k hpos (Nat.lt_succ_self k)
        have halpha : M.faceOf (M.alpha ((M.sigma ^ k) (M.alpha d))) ∈ faces := by
          by_contra hout
          have hb : IsBoundaryDart M faces ((M.sigma ^ k) (M.alpha d)) :=
            show M.faceOf ((M.sigma ^ k) (M.alpha d)) ∈ faces ∧
              M.faceOf (M.alpha ((M.sigma ^ k) (M.alpha d))) ∉ faces from ⟨hy, hout⟩
          exact hoff (show (M.sigma ^ k) (M.alpha d) ∈ B.cycle ∨
            M.alpha ((M.sigma ^ k) (M.alpha d)) ∈ B.cycle from
            Or.inl ((B.cycle_mem_iff _).mpr hb))
        have hstep : M.facePerm (M.alpha ((M.sigma ^ k) (M.alpha d))) =
            (M.sigma ^ (k + 1)) (M.alpha d) := by
          change M.sigma (M.alpha (M.alpha ((M.sigma ^ k) (M.alpha d)))) =
            (M.sigma ^ (k + 1)) (M.alpha d)
          rw [M.alpha_involutive ((M.sigma ^ k) (M.alpha d)), pow_succ', Perm.mul_apply]
        rw [← hstep, M.faceOf_facePerm]
        exact halpha

/-- **The turning condition for a boundary cycle.**  Rotating from the reversal of a listed dart,
the first dart on an edge of the listing is a listed dart. -/
theorem turn_mem_cycle (B : BoundaryCycle M faces) {d : M.Dart} (hd : d ∈ B.cycle) (m : ℕ)
    (hm : 0 < m) (hkeep : walkKeep M B.cycle ((M.sigma ^ m) (M.alpha d)))
    (havoid : ∀ k, 0 < k → k < m → ¬ walkKeep M B.cycle ((M.sigma ^ k) (M.alpha d))) :
    (M.sigma ^ m) (M.alpha d) ∈ B.cycle := by
  have hface := B.faceOf_sigma_pow_alpha_mem hd m hm havoid
  have hkeep' : (M.sigma ^ m) (M.alpha d) ∈ B.cycle ∨
      M.alpha ((M.sigma ^ m) (M.alpha d)) ∈ B.cycle := hkeep
  rcases hkeep' with hmem | hrev
  · exact hmem
  · have hb : M.faceOf (M.alpha ((M.sigma ^ m) (M.alpha d))) ∈ faces ∧
        M.faceOf (M.alpha (M.alpha ((M.sigma ^ m) (M.alpha d)))) ∉ faces :=
      (B.cycle_mem_iff _).mp hrev
    rw [M.alpha_involutive ((M.sigma ^ m) (M.alpha d))] at hb
    exact absurd hface hb.2

/-- **A boundary cycle in walk order is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk (B : BoundaryCycle M faces)
    (hchain : B.cycle.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : M.vertexOf (M.alpha (B.cycle.getLast B.cycle_nonempty)) =
      M.vertexOf (B.cycle.head B.cycle_nonempty)) :
    IsNoncrossingClosedWalk M B.cycle where
  ne_nil := B.cycle_nonempty
  nodup := B.cycle_nodup
  chain := hchain
  closes := hcloses
  alpha_not_mem d hd := fun hrev => by
    have hb : M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces := (B.cycle_mem_iff d).mp hd
    have hb' : M.faceOf (M.alpha d) ∈ faces ∧ M.faceOf (M.alpha (M.alpha d)) ∉ faces :=
      (B.cycle_mem_iff _).mp hrev
    exact hb.2 hb'.1
  turn_mem d hd m hm hkeep havoid := B.turn_mem_cycle hd m hm hkeep havoid

end Surgery.MapCollapse.BoundaryCycle

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket face set in walk order is a noncrossing closed walk.** -/
theorem ClosedWalk.isNoncrossingClosedWalk {K : PocketFaceSet D eps X lo hi}
    (hK : K.ClosedWalk) : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle := by
  obtain ⟨hchain, hcloses⟩ := hK
  exact K.boundary.isNoncrossingClosedWalk hchain hcloses

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.faceOf_sigma_pow_alpha_mem
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.turn_mem_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.isNoncrossingClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.ClosedWalk.isNoncrossingClosedWalk
