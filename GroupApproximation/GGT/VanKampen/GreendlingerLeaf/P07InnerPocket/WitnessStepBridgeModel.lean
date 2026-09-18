import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeLift
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeFirstReturn
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedRotate
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-61: the reclosed mirror is a planar model of the curve

Lane gl-p07-61.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepBridge_turn`: a cyclic step `(x, y)` of `invDarts X outerWalk` is a first-kept turn
  `σ ^ m y = α x` of `X`, with no dart of the walk (or its reverse) in between.  This is
  `turn_next` of `EnclosedFaceSetSucc`, read backwards.
* `witnessStepBridge_succ_of_turn`: such a turn between kept darts of a boundary cycle `B` is a
  `WitnessStepGenusSucc` step of the mirror of the reclosed map.  The reclosed rotation is the first
  return of `σ` to the kept darts (`reclosed_sigma_firstReturn`), so its intermediate darts are
  intermediate darts of the old turn, and none of them is on the walk.
* `witnessStepBridge_model`: from a boundary cycle `B` that follows its boundary, carries the walk
  and has the order of `w` on the walk, the conclusion of `WitnessStepGenusBridgeStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A cyclic step of the inverse walk is a first-kept turn of the diagram.** -/
theorem witnessStepBridge_turn {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow) {n : ℕ}
    {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t) :
    ∃ m, 0 < m ∧ (X.toCombMap.sigma ^ m) y = X.toCombMap.alpha x ∧
      ∀ k, 0 < k → k < m → ¬ walkKeep X.toCombMap ow ((X.toCombMap.sigma ^ k) y) := by
  have h' : (ow.reverse.map X.toCombMap.alpha).rotate n = s ++ x :: y :: t := h
  obtain ⟨s', t', x', y', hr, rfl, rfl⟩ := witnessStepGenus_rotate_lift X.toCombMap.alpha _ h'
  rw [List.rotate_reverse] at hr
  have h2 : ow.rotate (ow.length - n % ow.length) = t'.reverse ++ y' :: x' :: s'.reverse := by
    rw [← List.reverse_reverse (ow.rotate (ow.length - n % ow.length)), hr]
    simp
  obtain ⟨K, hK⟩ : ∃ K, ow.rotate K = (y' :: x' :: s'.reverse) ++ t'.reverse :=
    ⟨(ow.length - n % ow.length) + t'.reverse.length, by
      rw [← List.rotate_rotate, h2, List.rotate_append_length_eq]⟩
  have hlen : 1 < (ow.rotate K).length := by
    rw [hK, List.length_append, List.length_cons, List.length_cons]
    omega
  have hi0 : 0 < (ow.rotate K).length := by omega
  have hg0 : (ow.rotate K)[0]'hi0 = y' :=
    (List.getElem_of_eq hK hi0).trans (by first | rfl | simp)
  have hmod : (0 + 1) % (ow.rotate K).length = 1 := by
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt hlen
  have hx1 : (ow.rotate K)[(0 + 1) % (ow.rotate K).length]'(Nat.mod_lt _ hi0) = x' :=
    (getElem_index_congr (ow.rotate K) hmod (Nat.mod_lt _ hi0) hlen).trans
      ((List.getElem_of_eq hK hlen).trans (by first | rfl | simp))
  obtain ⟨m, hm, hkeep, hfirst⟩ :=
    PocketRun.exists_firstKeep (ow.rotate K) (List.getElem_mem hi0)
  have ht := ((EnclosedFaceSetSucc.rotate E K).turn_next 0 hi0 m hm hkeep hfirst).trans hx1
  rw [hg0] at ht
  rw [walkKeep_rotate_eq, hg0] at hfirst
  refine ⟨m, hm, ?_, hfirst⟩
  rw [X.toCombMap.alpha_involutive x']
  exact ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_turn

/-- **A first-kept turn between kept darts is a successor step of the reclosed mirror.** -/
theorem witnessStepBridge_succ_of_turn (M : CombMap.{v}) (O : Finset M.Face)
    (B : BoundaryCycle M O) (hwalk : B.FollowsBoundary) (ow : List M.Dart)
    (l' : List (KeptDart M O)) (hl' : ∀ z ∈ l', M.alpha z.1 ∈ ow) (c d : KeptDart M O)
    (m : ℕ) (hm : 0 < m) (hσ : (M.sigma ^ m) d.1 = M.alpha c.1)
    (hnot : ∀ k, 0 < k → k < m → ¬ walkKeep M ow ((M.sigma ^ k) d.1)) :
    WitnessStepGenusSucc (witnessStepBridge_mirror (reclosedMap M O B)) l' c d := by
  obtain ⟨m', hm', hq, hmid⟩ := witnessStepBridge_firstReturn_iterate
    (reclosed_sigma_firstReturn M O B hwalk) m d ((reclosedMap M O B).alpha c) hm hσ
  refine ⟨m', hm', ?_, ?_⟩
  · change ((reclosedMap M O B).sigma⁻¹ ^ m') ((reclosedMap M O B).alpha c) = d
    rw [← hq, inv_pow]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  · intro k hk hkm
    obtain ⟨r, rfl⟩ : ∃ r, m' = k + r := ⟨m' - k, by omega⟩
    obtain ⟨j, hj, hjm, hje⟩ := hmid r (by omega) (by omega)
    have hval : Subtype.val (((reclosedMap M O B).sigma⁻¹ ^ k) ((reclosedMap M O B).alpha c)) =
        (M.sigma ^ j) d.1 := by
      rw [← hq, witnessStepBridge_inv_pow_apply]
      exact hje
    have hclaim : ∀ z : KeptDart M O, z.1 = (M.sigma ^ j) d.1 →
        z ∉ l' ∧ keptAlpha M O z ∉ l' := by
      intro z hz
      refine ⟨fun hz' => hnot j hj hjm (Or.inr ?_), fun hz' => hnot j hj hjm (Or.inl ?_)⟩
      · rw [← hz]
        exact hl' z hz'
      · have h1 : M.alpha (M.alpha z.1) ∈ ow := hl' _ hz'
        rw [M.alpha_involutive z.1] at h1
        rw [← hz]
        exact h1
    exact hclaim _ hval

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_succ_of_turn
