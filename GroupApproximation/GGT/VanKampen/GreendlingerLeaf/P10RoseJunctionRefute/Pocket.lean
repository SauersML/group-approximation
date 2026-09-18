import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Area
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket face set of the 24-dart counterexample

Lane gl-p10-51.

The pocket face set `roseJunctionRefute_pK` has the faces `[0]`, `[2,16,6,18]`, `[4]`,
`[8,20,12,22]` and `[10]`, source `S` and kept cell `K₀`.  Its boundary cycle is
`[0,2,16,4,6,18,8,20,10,12,22]`:
* first side `[0]`;
* source arc `[19,7,5,17,3]` of `S`, read backwards as `[2,16,4,6,18]`;
* empty second side;
* target arc `[8,20,10,12,22]` of the exterior boundary `[8,20,10,12,22,14]`, between the
  positions `0` and `5`.

Proof route: `decide` on the listed darts.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)

theorem roseJunctionRefute_cellDarts :
    Embedded.cellDarts roseJunctionRefute_X roseJunctionRefute_iS = [19, 7, 5, 17, 3, 14, 1] := by
  change (roseJunctionRefute_boundary (roseJunctionRefute_face 1)).darts = _
  rw [roseJunctionRefute_bd_face]
  rfl

theorem roseJunctionRefute_outerDarts :
    Embedded.outerDarts roseJunctionRefute_X = [8, 20, 10, 12, 22, 14] := by
  change ((roseJunctionRefute_boundary (roseJunctionRefute_face 5)).darts.reverse.map
    roseJunctionRefute_M.alpha) = _
  rw [roseJunctionRefute_bd_face]
  rfl

/-- The arc `[19,7,5,17,3]` of `S`. -/
def roseJunctionRefute_sArc :
    Embedded.CyclicArc (Embedded.cellDarts roseJunctionRefute_X roseJunctionRefute_iS) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 5
  length_le := by
    rw [roseJunctionRefute_cellDarts]
    decide

theorem roseJunctionRefute_sArc_darts : roseJunctionRefute_sArc.darts = [19, 7, 5, 17, 3] := by
  change ((Embedded.cellDarts roseJunctionRefute_X roseJunctionRefute_iS).drop 0 ++
    (Embedded.cellDarts roseJunctionRefute_X roseJunctionRefute_iS).take 0).take 5 = _
  rw [roseJunctionRefute_cellDarts]
  rfl

/-- The arc `[8,20,10,12,22]` of the exterior boundary `[8,20,10,12,22,14]`. -/
def roseJunctionRefute_tArc : Embedded.CyclicArc (Embedded.outerDarts roseJunctionRefute_X) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 5
  length_le := by
    rw [roseJunctionRefute_outerDarts]
    decide

theorem roseJunctionRefute_tArc_darts : roseJunctionRefute_tArc.darts = [8, 20, 10, 12, 22] := by
  change ((Embedded.outerDarts roseJunctionRefute_X).drop 0 ++
    (Embedded.outerDarts roseJunctionRefute_X).take 0).take 5 = _
  rw [roseJunctionRefute_outerDarts]
  rfl

/-- Membership of the faces `0, …, 6` in the pocket face set. -/
def roseJunctionRefute_faceIn : Fin 7 → Bool := ![true, false, true, true, true, false, true]

/-- The faces `[0]`, `[2,16,6,18]`, `[4]`, `[8,20,12,22]` and `[10]`. -/
noncomputable def roseJunctionRefute_pFaces : Finset roseJunctionRefute_M.Face :=
  ({0, 2, 3, 4, 6} : Finset (Fin 7)).map roseJunctionRefute_faceEquiv.symm.toEmbedding

theorem roseJunctionRefute_faceMem (i : Fin 7) :
    roseJunctionRefute_face i ∈ roseJunctionRefute_pFaces ↔ roseJunctionRefute_faceIn i = true := by
  unfold roseJunctionRefute_pFaces
  rw [Finset.mem_map_equiv, Equiv.symm_symm, roseJunctionRefute_faceEquiv_face]
  revert i
  decide

def roseJunctionRefute_cyc : List (Fin 24) := [0, 2, 16, 4, 6, 18, 8, 20, 10, 12, 22]

theorem roseJunctionRefute_bd_iff (d : Fin 24) :
    IsBoundaryDart roseJunctionRefute_X.toCombMap roseJunctionRefute_pFaces d ↔
      d ∈ roseJunctionRefute_cyc := by
  change roseJunctionRefute_M.faceOf d ∈ roseJunctionRefute_pFaces ∧
    roseJunctionRefute_M.faceOf (roseJunctionRefute_M.alpha d) ∉ roseJunctionRefute_pFaces ↔ _
  rw [roseJunctionRefute_faceOf_eq_face', roseJunctionRefute_faceOf_eq_face',
    roseJunctionRefute_faceMem, roseJunctionRefute_faceMem]
  revert d
  decide

/-- The boundary darts of the pocket face set, in walk order. -/
def roseJunctionRefute_pCycle :
    BoundaryCycle roseJunctionRefute_X.toCombMap roseJunctionRefute_pFaces where
  cycle := roseJunctionRefute_cyc
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : roseJunctionRefute_cyc.Nodup)
  cycle_mem_iff := fun d => (roseJunctionRefute_bd_iff d).symm

theorem roseJunctionRefute_decomp : roseJunctionRefute_pCycle.cycle =
    ([0] : List roseJunctionRefute_X.toCombMap.Dart) ++
      Embedded.invDarts roseJunctionRefute_X roseJunctionRefute_sArc.darts ++
        ([] : List roseJunctionRefute_X.toCombMap.Dart) ++ roseJunctionRefute_tArc.darts := by
  rw [roseJunctionRefute_sArc_darts, roseJunctionRefute_tArc_darts]
  decide

theorem roseJunctionRefute_sideNorm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord roseJunctionRefute_X ([0] : List roseJunctionRefute_X.toCombMap.Dart))) ≤
      1 := by
  have hmem : RelLetter.listVal (Embedded.dartWord roseJunctionRefute_X
      ([0] : List roseJunctionRefute_X.toCombMap.Dart)) ∈ D.alphabet.carrier :=
    Or.inl (Set.mem_univ _)
  exact WordMetric.wordNorm_le_one_of_mem hmem

theorem roseJunctionRefute_emptyNorm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord roseJunctionRefute_X ([] : List roseJunctionRefute_X.toCombMap.Dart))) ≤
      1 :=
  (Nat.le_of_eq (WordMetric.wordNorm_one _)).trans (Nat.zero_le 1)

/-- **The pocket face set** at `ε = 1` between the positions `0` and `5`. -/
noncomputable def roseJunctionRefute_pK : PocketFaceSet D 1 roseJunctionRefute_X 0 5 where
  faces := roseJunctionRefute_pFaces
  outerFace_not_mem := fun h => absurd ((roseJunctionRefute_faceMem 5).mp h) (by decide)
  source := roseJunctionRefute_iS
  source_not_mem := fun h => absurd ((roseJunctionRefute_faceMem 1).mp h) (by decide)
  kept := roseJunctionRefute_iK0
  kept_mem := (roseJunctionRefute_faceMem 0).mpr rfl
  sourceArc := roseJunctionRefute_sArc
  targetArc := roseJunctionRefute_tArc
  firstSide := [0]
  secondSide := []
  boundary := roseJunctionRefute_pCycle
  decomposition := roseJunctionRefute_decomp
  firstSide_length_le := le_refl 1
  secondSide_length_le := Nat.zero_le _
  firstSide_norm_le := roseJunctionRefute_sideNorm
  secondSide_norm_le := roseJunctionRefute_emptyNorm
  lo_le := Nat.zero_le _
  le_hi := by decide

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
