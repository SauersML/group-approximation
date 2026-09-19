import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# The turns of the exclusive pocket walk are first turns

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.7(b): the subdiagram `Γ¹` with
`∂Γ¹ = s₁ t₁ s₂ t₂`.  Route `research/nm-exclusive-pocket-first-turns.md`: take the pocket
strictly between two exterior regions `x`, `y` of the cell `Π`.  Its walk reads the inner side of
`y`, the gap arc of `∂Π`, the inner side of `x`, and the stretch of `∂Δ` between the two target
arcs, and every turn of it is a first turn:

* along a side, the turn is a boundary walk of the region, reversed;
* along an arc, it is a face step of `Π` or of the exterior face, reversed;
* at a junction, it is a face step followed by a boundary walk of the region, or the reverse.

So the pocket is in first-turn order (`PocketFaceSet.FirstTurns`), and the landed first-turn pinch
applies to it.  This module proves the turn lemmas, for a face set `R` none of whose internal
darts lies on the walk.

* `ExclusiveTurns.not_walkKeep_of_internalDart`: an internal dart of `R` is off the edges of `c`
  when no dart of `c` is internal to `R`.
* `ExclusiveTurns.firstTurn_of_boundaryWalk`: a boundary walk of `R` is a first turn.
* `ExclusiveTurns.firstTurn_trans`: two first turns joined at a dart off the edges of `c`.
* `ExclusiveTurns.firstTurn_sigma_boundaryWalk`, `ExclusiveTurns.firstTurn_boundaryWalk_sigma`:
  the two junction shapes.
* `ExclusiveTurns.isChain_reverse_map_alpha` and its two instances `_of_boundaryWalk`,
  `_of_facePerm`: a stretch of first turns, of boundary walks of `R`, or of face steps, read
  backwards on the reversed darts, satisfies the chain condition of `PocketFaceSet.FirstTurns`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

namespace ExclusiveTurns

variable {M : CombMap.{u}} {c : List M.Dart} {R : Finset M.Face}

/-- The reversal of an internal dart is internal. -/
theorem internalDart_alpha {z : M.Dart} (hz : InternalDart M R z) :
    InternalDart M R (M.alpha z) := by
  unfold InternalDart at hz ⊢
  rw [M.alpha_involutive z]
  exact ⟨hz.2, hz.1⟩

/-- **An internal dart of `R` is off the edges of `c`**, when no dart of `c` is internal to
`R`. -/
theorem not_walkKeep_of_internalDart (hc : ∀ d ∈ c, ¬ InternalDart M R d) {z : M.Dart}
    (hz : InternalDart M R z) : ¬ walkKeep M c z := by
  rintro (hmem | hmem)
  · exact hc z hmem hz
  · exact hc _ hmem (internalDart_alpha hz)

/-- **A boundary walk of `R` is a first turn** along the edges of any `c` with no dart internal
to `R`: the darts it rotates past are internal to `R`. -/
theorem firstTurn_of_boundaryWalk (hc : ∀ d ∈ c, ¬ InternalDart M R d) {x y : M.Dart}
    (h : BoundaryWalk M R x y) : FirstTurn M c x y := by
  obtain ⟨n, hn, hskip⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M R) h
  refine ⟨n + 1, Nat.succ_pos n, ?_, fun t ht htn => ?_⟩
  · rw [pow_succ, Perm.mul_apply]
    exact hn
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [pow_succ, Perm.mul_apply]
    exact not_walkKeep_of_internalDart hc (hskip s (by omega))

/-- **Two first turns joined at a dart off the edges of `c`** make one first turn. -/
theorem firstTurn_trans {x z y : M.Dart} (h₁ : FirstTurn M c x z) (hz : ¬ walkKeep M c z)
    (h₂ : FirstTurn M c (M.alpha z) y) : FirstTurn M c x y := by
  obtain ⟨k, _hk, hkz, hkoff⟩ := h₁
  obtain ⟨m, hm, hmy, hmoff⟩ := h₂
  rw [M.alpha_involutive z] at hmy hmoff
  refine ⟨m + k, Nat.lt_of_lt_of_le hm (Nat.le_add_right m k), ?_, fun t ht htk => ?_⟩
  · rw [pow_add, Perm.mul_apply, hkz, hmy]
  · rcases lt_trichotomy t k with hlt | hteq | hgt
    · exact hkoff t ht hlt
    · rw [hteq, hkz]
      exact hz
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + k := ⟨t - k, by omega⟩
      rw [pow_add, Perm.mul_apply, hkz]
      exact hmoff s (by omega) (by omega)

/-- **A junction, arc first**: a face step onto a dart `z` off the edges of `c`, then a boundary
walk of `R` from the reversal of `z`. -/
theorem firstTurn_sigma_boundaryWalk (hc : ∀ d ∈ c, ¬ InternalDart M R d) {x z y : M.Dart}
    (hxz : M.sigma (M.alpha x) = z) (hz : ¬ walkKeep M c z)
    (h : BoundaryWalk M R (M.alpha z) y) : FirstTurn M c x y :=
  firstTurn_trans (FirstTurn.of_sigma_alpha hxz) hz (firstTurn_of_boundaryWalk hc h)

/-- **A junction, region first**: a boundary walk of `R` onto a dart `z` off the edges of `c`,
then one rotation step. -/
theorem firstTurn_boundaryWalk_sigma (hc : ∀ d ∈ c, ¬ InternalDart M R d) {x z y : M.Dart}
    (h : BoundaryWalk M R x z) (hz : ¬ walkKeep M c z) (hzy : M.sigma z = y) :
    FirstTurn M c x y :=
  firstTurn_trans (firstTurn_of_boundaryWalk hc h) hz
    (FirstTurn.of_sigma_alpha (by rw [M.alpha_involutive z]; exact hzy))

/-- **A stretch of first turns, read backwards on the reversed darts**, satisfies the chain
condition of `PocketFaceSet.FirstTurns`: from each dart `d` into the next dart `e`, a first turn
from `alpha e` to `alpha d`. -/
theorem isChain_reverse_map_alpha {l : List M.Dart} (hl : l.IsChain (FirstTurn M c)) :
    (l.reverse.map M.alpha).IsChain (fun d e => FirstTurn M c (M.alpha e) (M.alpha d)) := by
  refine (List.isChain_map M.alpha).2 (List.isChain_reverse.2 ?_)
  refine hl.imp fun a b h => ?_
  show FirstTurn M c (M.alpha (M.alpha a)) (M.alpha (M.alpha b))
  rw [M.alpha_involutive a, M.alpha_involutive b]
  exact h

/-- **A stretch of a region's boundary walk, read backwards on the reversed darts** (an inner
side of the exclusive pocket), satisfies the chain condition of `PocketFaceSet.FirstTurns`. -/
theorem isChain_reverse_map_alpha_of_boundaryWalk (hc : ∀ d ∈ c, ¬ InternalDart M R d)
    {l : List M.Dart} (hl : l.IsChain (BoundaryWalk M R)) :
    (l.reverse.map M.alpha).IsChain (fun d e => FirstTurn M c (M.alpha e) (M.alpha d)) :=
  isChain_reverse_map_alpha (hl.imp fun _ _ h => firstTurn_of_boundaryWalk hc h)

/-- **A stretch of face steps, read backwards on the reversed darts** (the gap arc of `∂Π`, or
the stretch of `∂Δ`), satisfies the chain condition of `PocketFaceSet.FirstTurns`. -/
theorem isChain_reverse_map_alpha_of_facePerm {l : List M.Dart}
    (hl : l.IsChain fun a b => M.facePerm a = b) :
    (l.reverse.map M.alpha).IsChain (fun d e => FirstTurn M c (M.alpha e) (M.alpha d)) :=
  isChain_reverse_map_alpha (hl.imp fun _ _ h => FirstTurn.of_facePerm h)

end ExclusiveTurns

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTurns.not_walkKeep_of_internalDart
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTurns.firstTurn_of_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTurns.firstTurn_trans
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTurns.firstTurn_sigma_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTurns.firstTurn_boundaryWalk_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTurns.isChain_reverse_map_alpha
#audit_axioms
  GroupApproximation.GGT.VanKampen.ExclusiveTurns.isChain_reverse_map_alpha_of_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTurns.isChain_reverse_map_alpha_of_facePerm
