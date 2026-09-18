import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCore
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchCorners
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# Tight passages of the rose cycle: first turns that cross nothing

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-19.

Write `σ` for the rotation and `α` for the reversal.  A passage `d → n` of the boundary cycle `c`
of a pocket (`n = next d`) is *tight* (`RegionMoveCoreCloseTight`) when `σ n = α d`: the two ends
of the passage are neighbours in the rotation at their vertex.  Every passage inside the target
arc `t₂` or inside `t₁⁻¹` is tight, because `σ (α x) = facePerm x` for a dart `x` of a face
boundary.  This module does not formalize that fact.

## Proofs

* `regionMoveCoreClose_firstTurn_of_sigma`: a tight turn is a first turn, with one rotation step
  and no intermediate darts to check.
* `regionMoveCoreClose_rotationBetween_iff`: if `σ n = z`, `x ≠ n` and `z ≠ y`, then `z` lies in
  the open rotation sector from `x` to `y` exactly when `n` does.
  *Proof.*  (→) Take `σ^a x = z` with `a > 0` and no `y` before it.  Then `σ^(a-1) x = n`
  (`σ` is injective).  Also `a - 1 > 0`, since `a = 1` would give `x = n`.  (←) Take
  `σ^a x = n`.  Then `σ^(a+1) x = z`, and the one new step does not meet `y`, since `z ≠ y`.
* `regionMoveCoreClose_looseCross`: in the rose configuration (`¬ K.FirstTurns` and
  `AllNonFirstTurnsCrossed K`), some non-first turn `d₀ → next d₀` is not tight and is crossed by a
  passage `d ≠ d₀` that is not tight either.
  *Proof.*  `PocketFaceSet.exists_not_firstTurn` gives a non-first turn `d₀`, which is not tight
  by the first lemma.  `AllNonFirstTurnsCrossed` gives a crosser `d`.  Suppose `d` were tight.
  Apply the sector lemma with `x = α d₀`, `y = next d₀`, `n = next d` and `z = α d`.  Its side
  conditions hold because the reversal of a boundary dart is not a boundary dart
  (`PocketFaceSet.boundary_alpha_not_mem`): `α d₀ ≠ next d` and `α d ≠ next d₀`.  So both ends of
  `d` would lie on the same side of the sector, and `d` would not cross.  Contradiction.

In particular the rose configuration has at least two distinct loose passages.  A pocket with at
most one loose passage (for instance `ε = 0` with one arc empty) never satisfies the rose premises.

## Truth check

These are proved lemmas.  Each only needs `σ` to be injective, and the reversal of a boundary dart
to lie off the boundary.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

/-- **A tight turn is a first turn**: one rotation step from `n` reaches `α d`. -/
theorem regionMoveCoreClose_firstTurn_of_sigma {M : CombMap.{v}} {c : List M.Dart}
    {n d : M.Dart} (h : M.sigma n = M.alpha d) : FirstTurn M c (M.alpha n) (M.alpha d) := by
  unfold FirstTurn
  refine ⟨1, Nat.one_pos, ?_, fun t ht hk => absurd hk (by omega)⟩
  rw [M.alpha_involutive n, pow_one]
  exact h

/-- **A tight passage lies on one side of every sector**: if `σ n = z`, `x ≠ n` and `z ≠ y`,
then `z` is strictly between `x` and `y` in the rotation exactly when `n` is. -/
theorem regionMoveCoreClose_rotationBetween_iff {M : CombMap.{v}} {x y n z : M.Dart}
    (hz : M.sigma n = z) (hx : x ≠ n) (hy : z ≠ y) :
    RotationBetween M x y z ↔ RotationBetween M x y n := by
  unfold RotationBetween
  constructor
  · rintro ⟨a, ha, hax, hb⟩
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hax' : (M.sigma ^ a) x = n := by
      rw [pow_succ', Equiv.Perm.mul_apply, ← hz] at hax
      exact M.sigma.injective hax
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [pow_zero, Equiv.Perm.one_apply] at hax'
      exact (hx hax').elim
    · exact ⟨a, hpos, hax', fun b hb1 hb2 => hb b hb1 (by omega)⟩
  · rintro ⟨a, -, hax, hb⟩
    refine ⟨a + 1, by omega, ?_, fun b hb1 hb2 => ?_⟩
    · rw [pow_succ', Equiv.Perm.mul_apply, hax, hz]
    · rcases Nat.lt_or_ge b (a + 1) with hlt | hge
      · exact hb b hb1 (by omega)
      · obtain rfl : b = a + 1 := by omega
        rw [pow_succ', Equiv.Perm.mul_apply, hax, hz]
        exact hy

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A tight passage** `d → next d` of the boundary cycle: `σ (next d) = α d`. -/
def RegionMoveCoreCloseTight (K : PocketFaceSet D eps X lo hi) (d : X.toCombMap.Dart)
    (hd : d ∈ K.boundary.cycle) : Prop :=
  X.toCombMap.sigma (K.boundary.cycle.next d hd) = X.toCombMap.alpha d

/-- **A loose crossing**: a non-first turn `d₀ → next d₀` that is not tight, crossed (in the sense
of `P10ChordLift.TurnCrossed`) by a passage `d ≠ d₀` that is not tight either. -/
def RegionMoveCoreCloseLooseCross (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle) (d : X.toCombMap.Dart)
    (hd : d ∈ K.boundary.cycle),
    P10ChordLift.NonFirstTurn K d₀ hd₀ ∧ ¬RegionMoveCoreCloseTight K d₀ hd₀ ∧ d ≠ d₀ ∧
      ¬RegionMoveCoreCloseTight K d hd ∧
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) ∧
      ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (K.boundary.cycle.next d hd))

/-- **A tight passage crosses no turn.** -/
theorem regionMoveCoreClose_not_crossed_of_tight (K : PocketFaceSet D eps X lo hi)
    {d₀ d : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) (hd : d ∈ K.boundary.cycle)
    (htd : RegionMoveCoreCloseTight K d hd) :
    (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (X.toCombMap.alpha d) ↔
      RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (K.boundary.cycle.next d hd)) := by
  have hx : X.toCombMap.alpha d₀ ≠ K.boundary.cycle.next d hd := by
    intro h
    apply K.boundary_alpha_not_mem hd₀
    rw [h]
    exact List.next_mem _ _ hd
  have hy : X.toCombMap.alpha d ≠ K.boundary.cycle.next d₀ hd₀ := by
    intro h
    apply K.boundary_alpha_not_mem hd
    rw [h]
    exact List.next_mem _ _ hd₀
  exact regionMoveCoreClose_rotationBetween_iff htd hx hy

/-- **The rose configuration has a loose crossing**: a pocket not in first-turn order, all of
whose non-first turns are crossed, has a non-first turn that is not tight, crossed by another
passage that is not tight either. -/
theorem regionMoveCoreClose_looseCross (K : PocketFaceSet D eps X lo hi)
    (hnft : ¬ K.FirstTurns) (hrose : P10ChordLift.AllNonFirstTurnsCrossed K) :
    RegionMoveCoreCloseLooseCross K := by
  obtain ⟨d₀, hd₀, hnf⟩ := K.exists_not_firstTurn hnft
  have hnt : ¬RegionMoveCoreCloseTight K d₀ hd₀ := fun ht =>
    hnf (regionMoveCoreClose_firstTurn_of_sigma ht)
  obtain ⟨d, hd, hne, hsc, hcross⟩ := hrose d₀ hd₀ hnf
  have htd : ¬RegionMoveCoreCloseTight K d hd := fun ht =>
    hcross (regionMoveCoreClose_not_crossed_of_tight K hd₀ hd ht)
  exact ⟨d₀, hd₀, d, hd, hnf, hnt, hne, htd, hsc, hcross⟩

/-- **The rose configuration has two distinct loose passages.** -/
theorem regionMoveCoreClose_exists_two_loose (K : PocketFaceSet D eps X lo hi)
    (hnft : ¬ K.FirstTurns) (hrose : P10ChordLift.AllNonFirstTurnsCrossed K) :
    ∃ (d₁ : X.toCombMap.Dart) (h₁ : d₁ ∈ K.boundary.cycle) (d₂ : X.toCombMap.Dart)
      (h₂ : d₂ ∈ K.boundary.cycle), d₁ ≠ d₂ ∧ ¬RegionMoveCoreCloseTight K d₁ h₁ ∧
        ¬RegionMoveCoreCloseTight K d₂ h₂ := by
  obtain ⟨d₀, hd₀, d, hd, -, hnt, hne, htd, -⟩ := regionMoveCoreClose_looseCross K hnft hrose
  exact ⟨d, hd, d₀, hd₀, hne, htd, hnt⟩

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_firstTurn_of_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_rotationBetween_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveCoreCloseTight
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveCoreCloseLooseCross
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_not_crossed_of_tight
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_looseCross
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_exists_two_loose
