import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Model14Diagram
import GroupApproximation.Manuscript.NonMF.Full.GL06f.Statement
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleavingModels
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The 14-dart shared-rose model: the pocket and the premises of the kept sub-walk core

The pocket face set `m14_pK` has the faces `K = [0,2]` and `P_B = [4,8,6]`, source `S` and
kept cell `K`.  Its boundary cycle is `[6,0,8,2,4]`:

* empty first side;
* source arc `[1,7]` of `S = [1,7,10]`, read backwards as `[6,0]`;
* second side `[8]` (the lake loop `ℓ`);
* target arc `[2,4]` of the exterior boundary `[4,13,2]`, between the positions `0` and `4`.

The contact vertex `v` is visited inside both arcs (first turns `6 → 0` and `2 → 4`); the vertex
`w` carries the three-passage rose `0 → 8`, `8 → 2`, `4 → 6`.  The pocket meets every hypothesis
of `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement`:

* `m14_closedWalk`, `m14_notFirst`, `m14_srcLt`, `m14_tgtLt`, `m14_notUnpinched`;
* `m14_allCrossed`: the three non-first turns at `w` are crossed by the passages of `4`, `0`
  and `8` (`Full.GL06f.AllNonFirstTurnsCrossed`).

Proof route: `decide` on the listed darts, and
`NoncrossingClosedWalkEulerNoninterleavingModels.not_rotationBetween_of_first` for the
crossings.  Same pattern as `P10RoseJunctionRefute/Pocket` and `P10RoseJunctionRefute/Premises`.

Manuscript status: infrastructure (a truth witness) for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)
open NoncrossingClosedWalkEulerNoninterleavingModels (not_rotationBetween_of_first)

theorem m14_cellDarts : Embedded.cellDarts m14_X m14_iS = [1, 7, 10] := by
  change (m14_boundary (m14_face 3)).darts = _
  rw [m14_bd_face]
  rfl

theorem m14_outerDarts : Embedded.outerDarts m14_X = [4, 13, 2] := by
  change ((m14_boundary (m14_face 5)).darts.reverse.map m14_M.alpha) = _
  rw [m14_bd_face]
  rfl

/-- The arc `[1,7]` of `S`. -/
def m14_sArc : Embedded.CyclicArc (Embedded.cellDarts m14_X m14_iS) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 2
  length_le := by
    rw [m14_cellDarts]
    decide

theorem m14_sArc_darts : m14_sArc.darts = [1, 7] := by
  change ((Embedded.cellDarts m14_X m14_iS).drop 0 ++
    (Embedded.cellDarts m14_X m14_iS).take 0).take 2 = _
  rw [m14_cellDarts]
  rfl

/-- The arc `[2,4]` of the exterior boundary `[4,13,2]`. -/
def m14_tArc : Embedded.CyclicArc (Embedded.outerDarts m14_X) where
  start := ⟨2, by rw [m14_outerDarts]; decide⟩
  length := 2
  length_le := by
    rw [m14_outerDarts]
    decide

theorem m14_tArc_darts : m14_tArc.darts = [2, 4] := by
  change ((Embedded.outerDarts m14_X).drop 2 ++ (Embedded.outerDarts m14_X).take 2).take 2 = _
  rw [m14_outerDarts]
  rfl

/-- Membership of the faces `0, …, 6` in the pocket face set. -/
def m14_faceIn : Fin 7 → Bool := ![true, true, false, false, false, false, false]

/-- The faces `K = [0,2]` and `P_B = [4,8,6]`. -/
noncomputable def m14_pFaces : Finset m14_M.Face :=
  ({0, 1} : Finset (Fin 7)).map m14_faceEquiv.symm.toEmbedding

theorem m14_faceMem (i : Fin 7) : m14_face i ∈ m14_pFaces ↔ m14_faceIn i = true := by
  unfold m14_pFaces
  rw [Finset.mem_map_equiv, Equiv.symm_symm, m14_faceEquiv_face]
  revert i
  decide

def m14_cyc : List (Fin 14) := [6, 0, 8, 2, 4]

theorem m14_bd_iff (d : Fin 14) : IsBoundaryDart m14_X.toCombMap m14_pFaces d ↔ d ∈ m14_cyc := by
  change m14_M.faceOf d ∈ m14_pFaces ∧ m14_M.faceOf (m14_M.alpha d) ∉ m14_pFaces ↔ _
  rw [m14_faceOf_eq_face', m14_faceOf_eq_face', m14_faceMem, m14_faceMem]
  revert d
  decide

/-- The boundary darts of the pocket face set, in walk order. -/
def m14_pCycle : BoundaryCycle m14_X.toCombMap m14_pFaces where
  cycle := m14_cyc
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : m14_cyc.Nodup)
  cycle_mem_iff := fun d => (m14_bd_iff d).symm

theorem m14_decomp : m14_pCycle.cycle =
    ([] : List m14_X.toCombMap.Dart) ++ Embedded.invDarts m14_X m14_sArc.darts ++
      ([8] : List m14_X.toCombMap.Dart) ++ m14_tArc.darts := by
  rw [m14_sArc_darts, m14_tArc_darts]
  decide

theorem m14_sideNorm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord m14_X ([8] : List m14_X.toCombMap.Dart))) ≤ 1 := by
  have hmem : RelLetter.listVal (Embedded.dartWord m14_X
      ([8] : List m14_X.toCombMap.Dart)) ∈ D.alphabet.carrier :=
    Or.inl (Set.mem_univ _)
  exact WordMetric.wordNorm_le_one_of_mem hmem

theorem m14_emptyNorm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord m14_X ([] : List m14_X.toCombMap.Dart))) ≤ 1 :=
  (Nat.le_of_eq (WordMetric.wordNorm_one _)).trans (Nat.zero_le 1)

/-- **The pocket face set** at `ε = 1` between the positions `0` and `4`. -/
noncomputable def m14_pK : PocketFaceSet D 1 m14_X 0 4 where
  faces := m14_pFaces
  outerFace_not_mem := fun h => absurd ((m14_faceMem 5).mp h) (by decide)
  source := m14_iS
  source_not_mem := fun h => absurd ((m14_faceMem 3).mp h) (by decide)
  kept := m14_iK
  kept_mem := (m14_faceMem 0).mpr rfl
  sourceArc := m14_sArc
  targetArc := m14_tArc
  firstSide := []
  secondSide := [8]
  boundary := m14_pCycle
  decomposition := m14_decomp
  firstSide_length_le := Nat.zero_le _
  secondSide_length_le := le_refl 1
  firstSide_norm_le := m14_emptyNorm
  secondSide_norm_le := m14_sideNorm
  lo_le := Nat.zero_le _
  le_hi := le_refl 4

/-- The successor of each dart of the boundary cycle (`0` off the cycle). -/
def m14_nxt : Fin 14 → Fin 14 := ![8, 0, 4, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0]

theorem m14_sameCycle (d e : Fin 14) (h : m14_vClass d = m14_vClass e) :
    m14_X.toCombMap.sigma.SameCycle d e :=
  (CombMap.vertexOf_eq_iff m14_X.toCombMap d e).mp ((m14_vClass_iff d e).mpr h)

theorem m14_srcLt :
    m14_pK.sourceArc.length < (Embedded.cellDarts m14_X m14_pK.source).length :=
  (by decide : (2 : ℕ) < 3).trans_eq (congrArg List.length m14_cellDarts).symm

theorem m14_tgtLt : m14_pK.targetArc.length < (Embedded.outerDarts m14_X).length :=
  (by decide : (2 : ℕ) < 3).trans_eq (congrArg List.length m14_outerDarts).symm

theorem m14_closedWalk : m14_pK.ClosedWalk := by
  have h : List.IsChain (fun d e : Fin 14 => m14_vClass (m14_M.alpha d) = m14_vClass e)
      m14_cyc := by
    decide
  refine ⟨h.imp (by intro a b hab; exact (m14_vClass_iff _ _).mpr hab),
    (m14_vClass_iff _ _).mpr ?_⟩
  decide

/-- The turn `0 → 8` is not a first turn: rotating from `8`, the walk dart `9 = α 8` comes
before `1 = α 0`. -/
theorem m14_notFirst : ¬m14_pK.FirstTurns := by
  intro hft
  obtain ⟨k, hk, hkv, ht⟩ := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp
    (show List.IsChain _ ((6 : m14_X.toCombMap.Dart) :: 0 :: [8, 2, 4]) from hft.1)).2).1
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · interval_cases k
    exact absurd hkv (by decide)
  · exact ht 1 (by decide) (by omega) (Or.inl (by decide))

theorem m14_notUnpinched :
    ¬Surgery.MapCollapse.Unpinched m14_X.toCombMap m14_pK.faces :=
  fun h => absurd (h 0 4 ((m14_bd_iff 0).mpr (by decide)) ((m14_bd_iff 4).mpr (by decide))
    ((m14_vClass_iff 0 4).mpr (by decide))) (by decide)

theorem m14_mem_cyc : ∀ d : m14_X.toCombMap.Dart,
    d ∈ m14_pK.boundary.cycle → d = 6 ∨ d = 0 ∨ d = 8 ∨ d = 2 ∨ d = 4 := by
  decide

theorem m14_next_eq (inst : DecidableEq m14_X.toCombMap.Dart) :
    ∀ d hd, @List.next _ inst m14_pK.boundary.cycle d hd = m14_nxt d := by
  obtain rfl : inst = m14_instDecEqX := Subsingleton.elim _ _
  decide

/-- **Every non-first turn of the pocket is crossed.** -/
theorem m14_allCrossed : GroupApproximation.Full.GL06f.AllNonFirstTurnsCrossed m14_pK := by
  intro d₀ hd₀ hnf
  unfold GroupApproximation.Full.GL06f.NonFirstTurn at hnf
  unfold GroupApproximation.Full.GL06f.TurnCrossed
  rcases m14_mem_cyc d₀ hd₀ with rfl | rfl | rfl | rfl | rfl
  · rw [m14_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · refine ⟨4, by decide, by decide, m14_sameCycle _ _ (by decide), ?_⟩
    rw [m14_next_eq, m14_next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 5) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨4, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · refine ⟨0, by decide, by decide, m14_sameCycle _ _ (by decide), ?_⟩
    rw [m14_next_eq, m14_next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 5) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨4, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · rw [m14_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · refine ⟨8, by decide, by decide, m14_sameCycle _ _ (by decide), ?_⟩
    rw [m14_next_eq, m14_next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 3) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨2, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_pK
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_notFirst
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_notUnpinched
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_allCrossed
