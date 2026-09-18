import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFaceChain
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.DartsNodup
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.PinchLoop
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shape: gap darts of a cell class lie off the polygon face

Osin (math/0411039v3, §9), Lemma 9.4, Case 1.  Lane `gl-p04-10`.  Let `Γ = P.face k` and let
class `i` of polygon `k` have kind `cell j`.  Every dart `g` in the gap after a side `s` of the
class satisfies `faceOf g ≠ Γ`.

## Proof

1. The gap after the last side is empty (`gap_last`), so a nonempty gap follows a side `s` that
   has a successor `s'` in the class, and `s' = (s + 1) % sideCount` (lane `gl-p04-02`,
   `ClassSidesSucc.classSides_isChain`).
2. Let `d` be the last dart of side `s` and `t` the first dart of side `s'`.  Then `φ d = t`
   (lane `gl-p04-03`, `SideSuccFace.facePerm_last`), and `d :: (gap s ++ [t])` is a contiguous
   block of the class darts.
3. The class darts satisfy `σ e = α x` for consecutive `x, e` (lane `gl-p04-01`,
   `ClassStep.sigma_succ`) and have no repeated dart (lane `gl-p04-09`,
   `DartsNodup.classDarts_nodup`).  The block inherits both properties (`pinch_chain`).
4. `d` lies on `Γ` (it is a side dart).  `α d` lies on relator cell `j`, because the class is the
   reversed arc `arc.darts.reverse.map α` of that cell (`cell_arc`), and that cell is not `Γ`
   (`face_not_cell`).  So `faceOf (α d) ≠ faceOf d`.
5. The planar pinch loop (`PinchLoop.faceOf_ne`) now gives `faceOf g ≠ faceOf d = Γ` for every
   `g` in the gap.  This is the corrected pinch lemma of truth check T6: it needs both no repeated
   dart and a different face across `d`, and both hold here.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

/-- **Gap darts of a cell class lie off the polygon face** (lane `gl-p04-10`).  For a class of
kind `cell j`, every dart in the gap after a side of the class lies on a face other than
`P.face k`. -/
theorem faceOf_gap_ne {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount) (hi : i < Q.classCount k)
    (hj : Q.classKind k i = .cell j) :
    ∀ s ∈ Q.classSides k i, ∀ g ∈ Q.gap k s, S.diagram.toCombMap.faceOf g ≠ P.face k := by
  intro s hs g hg
  have hgap : Q.gap k s ≠ [] := List.ne_nil_of_mem hg
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem hs
  rcases L2 with _ | ⟨s', L3⟩
  · exact absurd (Q.gap_last k i hi s (Option.mem_def.mpr (by rw [hL, List.getLast?_concat])))
      hgap
  -- the successor side `s'`
  have hs_lt : s < P.sideCount k := Q.lt_sideCount_of_mem k i hi s hs
  have hs'mem : s' ∈ Q.classSides k i := by simp [hL]
  have hs'_lt : s' < P.sideCount k := Q.lt_sideCount_of_mem k i hi s' hs'mem
  have hinfS : [s, s'] <:+: Q.classSides k i := ⟨L1, L3, by simp [hL]⟩
  have hsucc : s' = (s + 1) % P.sideCount k :=
    (List.isChain_cons_cons.mp ((ClassSidesSucc.classSides_isChain Q k i hi).infix hinfS)).1
  -- the last dart `d` of side `s` and the first dart `t` of side `s'`
  obtain ⟨A, d, hsd⟩ : ∃ A d, P.sideDarts k s = A ++ [d] :=
    ⟨_, _, (List.dropLast_concat_getLast (P.side_ne_nil k s hs_lt)).symm⟩
  obtain ⟨t, B, hsd'⟩ := List.exists_cons_of_ne_nil (P.side_ne_nil k s' hs'_lt)
  have hd : (P.sideDarts k s).getLast? = some d := by rw [hsd, List.getLast?_concat]
  have ht : (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some t := by
    rw [← hsucc, hsd', List.head?_cons]
  have hdt : S.diagram.toCombMap.facePerm d = t :=
    SideSuccFace.facePerm_last Q k s hs_lt d t hd ht
  -- the block `d :: (gap s ++ [t])` of the class darts
  have hinf : (d :: (Q.gap k s ++ [t])) <:+: Q.classDarts k i := by
    refine ⟨(L1.flatMap fun x => P.sideDarts k x ++ Q.gap k x) ++ A,
      B ++ Q.gap k s' ++ L3.flatMap fun x => P.sideDarts k x ++ Q.gap k x, ?_⟩
    simp only [OsinLemma94ClassPolygons.classDarts, hL, List.flatMap_append, List.flatMap_cons,
      hsd, hsd', List.append_assoc, List.cons_append, List.nil_append]
  have hchain : (Q.classDarts k i).IsChain
      fun a b => S.diagram.toCombMap.sigma b = S.diagram.toCombMap.alpha a :=
    List.isChain_iff_getElem.mpr fun n hn =>
      ClassStep.sigma_succ Q k i j hi hj n _ _ (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem hn)
  obtain ⟨hγchain, hhead, hlast⟩ := pinch_chain hgap (hchain.infix hinf)
  have hnodup : (d :: (Q.gap k s ++ [t])).Nodup :=
    List.Nodup.sublist hinf.sublist (DartsNodup.classDarts_nodup Q k i j hi hj)
  -- `d` lies on `Γ`, and the face across `d` is relator cell `j`
  have hdface : S.diagram.toCombMap.faceOf d = P.face k :=
    SameCellPocketSides.faceOf_of_mem_rotate (P.walk k)
      (List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hs_lt, by rw [hsd]; exact List.mem_concat_self⟩)
  obtain ⟨arc, harc⟩ := Q.cell_arc k i j hi hj
  have hd_rev : d ∈ arc.reverseDarts := by
    rw [← harc]
    exact hinf.subset List.mem_cons_self
  have hαmem : S.diagram.toCombMap.alpha d ∈ arc.darts := by
    change d ∈ arc.darts.reverse.map S.diagram.toCombMap.alpha at hd_rev
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd_rev
    rw [S.diagram.toCombMap.alpha_involutive x]
    exact List.mem_reverse.mp hx
  have hαface : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) =
      (Embedded.cell S.diagram j).face :=
    ((S.diagram.faceBoundary (Embedded.cell S.diagram j).face).mem_iff _).mp
      (arc.mem_cycle_of_mem_darts hαmem)
  have hface : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ≠
      S.diagram.toCombMap.faceOf d := by
    rw [hαface, hdface]
    exact P.face_not_cell k j
  have key := PinchLoop.faceOf_ne S.diagram.toCombMap S.diagram.planar (Q.gap k s) d t hgap
    hnodup hγchain hhead hdt hlast hface g hg
  rwa [hdface] at key

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace.faceOf_gap_ne

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace
