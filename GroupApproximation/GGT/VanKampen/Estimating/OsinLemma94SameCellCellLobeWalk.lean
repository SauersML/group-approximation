import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellCellLobeValue
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketIsland
import GroupApproximation.Meta.AxiomGuard

/-!
# The walk-level X-pocket whose carrier part repeats a vertex: the two lobe cases, and the first

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`, at walk level
(`OsinLemma94CaseOneXWalkStatementOf`): a closed walk `s ++ invDarts B` with `s` a sublist of
`invDarts X` with its value, and the exterior face off its side.  This module treats the shape
`OsinLemma94CaseOneWalkCellPinchStatement`, where the carrier part `invDarts B` repeats a vertex.

* `osinLemma94CaseOneWalkCellPinch_of_lobes`: the carrier part has an innermost lobe `L`
  (`ClosedWalkInnermostLobe.exists_innermost_lobe`), and the shape statement follows from the case
  where `L` reads an element other than `1` (`OsinLemma94CaseOneWalkCellLobeValueStatement`) and the
  case where it reads `1` (`OsinLemma94CaseOneWalkCellLobeExcisionStatement`).
* `SameCellCellLobe.outerFace_not_mem_sideFaces_lobe_of_walk`: the exterior face is off the side of
  `L`.  As in `SameCellCellLobe.outerFace_not_mem_sideFaces_lobe`, with the face part `s` in place of
  `invDarts X`: every dart of `s` reverses a dart of `X`, which lies on the polygon face.
* `osinLemma94CaseOneWalkCellLobeValue : OsinLemma94CaseOneWalkCellLobeValueStatement`, closed: the
  walk-level loop-cut kill `SameCellSimplePocket.false_of_simpleWalk_of_below` with an empty side.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **The walk-level X-pocket whose carrier part has an innermost lobe reading an element other
than `1`.** -/
def OsinLemma94CaseOneWalkCellLobeValueStatement : Prop :=
  OsinLemma94CaseOneXWalkStatementOf.{u, w, v} fun Delta s b =>
    PocketWalkCellLobeValueShape Delta s b

/-- **The walk-level X-pocket whose carrier part has an innermost lobe reading `1`.** -/
def OsinLemma94CaseOneWalkCellLobeExcisionStatement : Prop :=
  OsinLemma94CaseOneXWalkStatementOf.{u, w, v} fun Delta s b =>
    PocketWalkCellLobeExcisionShape Delta s b

/-- **The walk-level X-pocket whose carrier part repeats a vertex, from its two lobe cases.** -/
theorem osinLemma94CaseOneWalkCellPinch_of_lobes
    (hvalue : OsinLemma94CaseOneWalkCellLobeValueStatement.{u, w, v})
    (hexcision : OsinLemma94CaseOneWalkCellLobeExcisionStatement.{u, w, v}) :
    OsinLemma94CaseOneWalkCellPinchStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e1, he1⟩ := hvalue D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e2, he2⟩ := hexcision D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨r1, hr1, h1⟩ := he1 eps (by omega)
  obtain ⟨r2, hr2, h2⟩ := he2 eps (by omega)
  refine ⟨max r1 r2, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB s hsub hwalk hsval hout
    hpinch
  have hwalk' := hwalk
  obtain ⟨_, hchainw, _⟩ := hwalk'
  have hchain : (invDarts S.diagram B).IsChain fun d e =>
      S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha d) =
        S.diagram.toCombMap.vertexOf e :=
    hchainw.right_of_append
  obtain ⟨l₁, L, l₂, hsplit, hL, hnodup⟩ :=
    ClosedWalkInnermostLobe.exists_innermost_lobe hchain hpinch
  by_cases hval : RelLetter.listVal (dartWord S.diagram L) = 1
  · exact h2 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB s hsub
      hwalk hsval hout ⟨l₁, L, l₂, hsplit, hL, hnodup, hval⟩
  · exact h1 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB s hsub
      hwalk hsval hout ⟨l₁, L, l₂, hsplit, hL, hnodup, hval⟩

namespace SameCellCellLobe

section Walk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- **The exterior face is off the side of a lobe of the carrier part of a walk-level pocket.** -/
theorem outerFace_not_mem_sideFaces_lobe_of_walk {f : Delta.toCombMap.Face}
    {j : Fin Delta.rCellCount} (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length)
    {s : List Delta.toCombMap.Dart} (hsX : ∀ z ∈ s, z ∈ invDarts Delta X)
    {l₁ L l₂ : List Delta.toCombMap.Dart} (hsplit : invDarts Delta B = l₁ ++ L ++ l₂)
    (hw : IsSimpleClosedWalk Delta.toCombMap L)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap (s ++ invDarts Delta B)) :
    Delta.outerFace ∉ sideFaces Delta.toCombMap L := by
  have hcell := cell_not_mem_sideFaces_lobe sourceArc targetArc hPi hsplit hw
  have hLB : ∀ d ∈ L, d ∈ invDarts Delta B := fun d hd => by
    rw [hsplit]
    exact List.mem_append_left _ (List.mem_append_right _ hd)
  obtain ⟨e, hePi, heF, heB, -, -, -⟩ :=
    SameCellPocketSides.exists_edge sourceArc targetArc htrav hPi hs
  have heL : ¬ walkKeep Delta.toCombMap L (Delta.toCombMap.alpha e) := by
    intro h
    unfold walkKeep at h
    rcases h with h | h
    · have hαα := SameCellPocketSides.alpha_mem_of_mem_invDarts (hLB _ h)
      rw [Delta.toCombMap.alpha_involutive e] at hαα
      exact heB hαα
    · rw [Delta.toCombMap.alpha_involutive e] at h
      have hαB := SameCellPocketSides.alpha_mem_of_mem_invDarts (hLB _ h)
      have hface := SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hαB)))
      exact hf (hface.symm.trans heF)
  intro hext
  refine hout (sideFaces_subset_of_agree (fun d hd => List.mem_append_right _ (hLB d hd)) ?_ hext)
  intro d hd y hdy hkw
  by_contra hkL
  have hdα : Relation.EqvGen (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap L))
      d (Delta.toCombMap.alpha y) :=
    Relation.EqvGen.trans _ _ _ hdy (Relation.EqvGen.rel _ _ (Or.inr ⟨hkL, rfl⟩))
  have hmem : ∀ z, (z = y ∨ z = Delta.toCombMap.alpha y) →
      z ∈ s ++ invDarts Delta B → False := by
    intro z hz hzw
    have hzα : Relation.EqvGen (CombMap.FaceClassStep Delta.toCombMap
        (walkKeep Delta.toCombMap L)) d (Delta.toCombMap.alpha z) := by
      rcases hz with rfl | rfl
      · exact hdα
      · rw [Delta.toCombMap.alpha_involutive y]
        exact hdy
    have hzw' : z ∈ invDarts Delta X ++ invDarts Delta B := by
      rcases List.mem_append.mp hzw with h | h
      · exact List.mem_append_left _ (hsX z h)
      · exact List.mem_append_right _ h
    rcases SameCellPocketSides.alpha_mem_of_mem_invDarts_append hzw' with hX | hB
    · have hfz : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) = f :=
        SameCellPocketSides.faceOf_of_mem_rotate htrav
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hX)))
      have hsame : Delta.toCombMap.facePerm.SameCycle (Delta.toCombMap.alpha z)
          (Delta.toCombMap.alpha e) :=
        (Delta.toCombMap.faceOf_eq_iff _ _).mp (hfz.trans heF.symm)
      have hdαe := Relation.EqvGen.trans _ _ _ hzα
        (eqvGen_faceClass_of_sameCycle Delta.toCombMap (walkKeep Delta.toCombMap L) hsame)
      have hde := Relation.EqvGen.trans _ _ _ hdαe
        (Relation.EqvGen.rel _ _ (Or.inr ⟨heL, rfl⟩))
      rw [Delta.toCombMap.alpha_involutive e] at hde
      apply hcell
      rw [← hePi]
      exact (mem_sideFaces_iff Delta.toCombMap L e).mpr ⟨d, hd, hde⟩
    · have hPiz := SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hB)))
      apply hcell
      rw [← hPiz]
      exact (mem_sideFaces_iff Delta.toCombMap L _).mpr ⟨d, hd, hzα⟩
  unfold walkKeep at hkw
  rcases hkw with h | h
  · exact hmem y (Or.inl rfl) h
  · exact hmem (Delta.toCombMap.alpha y) (Or.inr rfl) h

end Walk

/-- **A lobe of the carrier part of a walk-level pocket reading an element other than `1`, refuted
below `Δ`.** -/
theorem false_of_walkCellLobe_value {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hs : 0 < sourceArc.length)
    {n : ℕ} {B A : List S.diagram.toCombMap.Dart}
    (hPi : (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    {s : List S.diagram.toCombMap.Dart} (hsub : s.Sublist (invDarts S.diagram X))
    (hout : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap (s ++ invDarts S.diagram B))
    (hshape : PocketWalkCellLobeValueShape S.diagram s (invDarts S.diagram B)) :
    False := by
  obtain ⟨l₁, L, l₂, hsplit, hL, hnodup, hval⟩ := hshape
  have hw := isSimpleClosedWalk_lobe hL hnodup hval
  obtain ⟨T, hT⟩ := exists_arc_of_lobe sourceArc targetArc hPi hsplit
  have hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram ([] : List S.diagram.toCombMap.Dart))) ≤ eps := by
    have h1 : RelLetter.listVal (dartWord S.diagram ([] : List S.diagram.toCombMap.Dart)) = 1 := by
      simp [Embedded.dartWord, RelLetter.listVal]
    rw [h1, WordMetric.wordNorm_one]
    exact Nat.zero_le _
  exact SameCellSimplePocket.false_of_simpleWalk_of_below hW hlambda hlambda1 hc hmu hmu1 hrho
    hlarge hleast hbelow S.equiv S.label_admissible hw
    (outerFace_not_mem_sideFaces_lobe_of_walk (P.face_not_cell k j) sourceArc targetArc htrav hPi
      hs (fun z hz => hsub.subset hz) hsplit hw hout)
    (cell_not_mem_sideFaces_lobe sourceArc targetArc hPi hsplit hw) T hT hnorm hval

end SameCellCellLobe

open SameCellSimplePocket SameCellCellLobe in
/-- **The walk-level X-pocket whose carrier part has a lobe reading an element other than `1`**,
closed. -/
theorem osinLemma94CaseOneWalkCellLobeValue :
    OsinLemma94CaseOneWalkCellLobeValueStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max 1 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k _C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj htrav hs _ht _hsource _htarget _hX _hY n B A hPi _hXB s hsub
    _hwalk _hsval hout hshape
  exact false_of_walkCellLobe_value hW hlambda hlambda1 hc hmu hmu1 (by omega)
    (hrho1 rho (le_of_max_le_right hrho)) hleast hbelow P k sourceArc targetArc htrav hs hPi hsub
    hout hshape

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalkCellPinch_of_lobes
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.outerFace_not_mem_sideFaces_lobe_of_walk
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.false_of_walkCellLobe_value
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalkCellLobeValue
