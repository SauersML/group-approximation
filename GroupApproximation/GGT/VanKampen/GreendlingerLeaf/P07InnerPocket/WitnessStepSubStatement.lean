import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSubNested
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeModel
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepLobeStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-65: the lobe sublist from the curve successor property

Lane gl-p07-65.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

## Route (planar, no Order / Cycle / Reclosed / Bridge)

Work in the mirror `M = (α, σ⁻¹)` of `X`, which is planar.  Let `w = witnessSublistCurve a b G₁ G₂`
and `l = invDarts X outerWalk`.
1. Membership: `l ⊆ w` (`hlab`, `witnessSublist_mem_curve`); both are duplicate free.
2. Every cyclic step of `l` is a successor step of `M` relative to `l`
   (`witnessStepSub_invDarts_succ`).  This is `witnessStepBridge_turn` read in the mirror.
3. Every cyclic step of `w` is a successor step of `M` relative to `w`.  This is the residual
   `witnessStepSub_CurveSuccStatement`.
4. Order: by the genus-zero split and first return, nested successor walks in a planar map are
   nested cyclically (`witnessStepSub_nested_sublist`).  So `l.rotate n <+ w`, and
   `l.rotate n = invDarts X (outerWalk.rotate (outerWalk.length - n % outerWalk.length))`.

## Status of the residual (LOUD)

`witnessStepSub_CurveSuccStatement` asserts, for the pocket curve `w` alone, that each cyclic
step `(x, y)` of `w` is a first-kept turn: `σ ^ m y = α x`, with no dart of `w` or its reverse
strictly between.
* **As a formula it is NOT weaker than `witnessStepLobe_SublistStatement`.** It keeps only the
  pocket premises (no relator cell `C`, no `outerWalk`, no `EnclosedFaceSetSucc`, no pinch) and
  it does not follow from the sublist conclusion.  With the reduction below it is **STRONGER**.
* **It is strictly SMALLER in proof content.**  It concerns the fixed curve `w` and the local
  vertex rotations at its corners only: no face set, no outer walk, no order relation.  It is NOT
  the Order, Cycle, Reclosed or Bridge statement, nor a restatement of one: those all speak about
  `outerWalk` and the lobe.  All order content is proved here from planarity.
* **Truth check** (`SP/gl-p07-65/succ_check.py` on the gl-p07-64 planar grid model with real
  pocket walks, noncrossing `K`, real witness and filtered curve; the Euler equalities are not
  modelled, so the test is stronger).  Seeds 11, 12, 13, 21, 22, 23: `w` is a cyclic mirror
  successor walk on all 1042 pocket walks (0 failures); in all 8031 lobe cases `l` is one too
  (0 failures).  Risk cases pass: 236 pinch-vertex curves, 129 shared-edge and 145 touching
  region pairs.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Each cyclic step of the inverse walk is a successor step of the mirror.** -/
theorem witnessStepSub_invDarts_succ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow) :
    ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
      (invDarts X ow).rotate n = s ++ x :: y :: t →
      WitnessStepGenusSucc (witnessStepBridge_mirror X.toCombMap) (invDarts X ow) x y := by
  intro n s t x y h
  obtain ⟨m, hm, hσ, hnot⟩ := witnessStepBridge_turn E h
  refine ⟨m, hm, ?_, ?_⟩
  · change (X.toCombMap.sigma⁻¹ ^ m) (X.toCombMap.alpha x) = y
    rw [← hσ, inv_pow]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  · intro k hk hkm
    show (X.toCombMap.sigma⁻¹ ^ k) (X.toCombMap.alpha x) ∉ invDarts X ow ∧
      X.toCombMap.alpha ((X.toCombMap.sigma⁻¹ ^ k) (X.toCombMap.alpha x)) ∉ invDarts X ow
    obtain ⟨r, rfl⟩ : ∃ r, m = k + r := ⟨m - k, by omega⟩
    have hval : (X.toCombMap.sigma⁻¹ ^ k) (X.toCombMap.alpha x) = (X.toCombMap.sigma ^ r) y := by
      rw [← hσ, witnessStepBridge_inv_pow_apply]
    rw [hval]
    have hr := hnot r (by omega) (by omega)
    refine ⟨fun hz => hr (Or.inr ((Embedded.mem_invDarts_iff _ _).mp hz)), fun hz => hr ?_⟩
    have h1 := (Embedded.mem_invDarts_iff _ _).mp hz
    rw [X.toCombMap.alpha_involutive] at h1
    exact Or.inl h1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_invDarts_succ
