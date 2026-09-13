import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatedInsertion
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatedInsertionProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingChains
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatingRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PendantRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.VanKampen.Estimating.UnboundNonemptyConnectors
import GroupApproximation.GGT.DGOPolygonGeodesicChain
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 2 of Osin's Lemma 9.4 from the separated insertion

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)`
is minimal."  The measure is the number of darts
(`GloballyDistinguishedSectionFamily.DartMinimal`).

Take a backwards connector pair (39) of a polygon whose target side is a cutting path.  From some
corner the walk of the polygon face reads `X ++ q ++ Y ++ p`.  Here `q` is the target segment from
`b'` to `b` and `p` is the source segment from `a` to `a'` (`CaseOneWalk.polygon_four_windows`).
The face lies across every dart of `q`, so the reverse darts of `q` lie on the walk.
* No dart of `q` has its reverse in `q` (`alpha_not_mem_of_dartMinimal`).
* The reverse darts of `p` lie on a relator cell, so no reverse dart of `q` lies in `p`.
* The walk across `q` runs back along it, so its reverse darts follow one another on the walk.
  They pass neither the first dart of `q` nor the first dart of `p`, so they all lie in `X` or all
  lie in `Y`.

The connector with the value of that stretch is nonempty and shorter than `ε`.  It is inserted
across the face (`SeparatedCornerInsertionInput`), and then `q` runs between two different
unselected `G`-faces and is removed (`separatingPathRemovalInput_of_pendant`).  The insertion adds
fewer than `2ε` darts, and the removal takes away `2 (b - b') > 2ε` darts, against `DartMinimal`.

`osinLemma94CaseTwoInput_of_insertion` proves `OsinLemma94CaseTwoInput` from
`SeparatedCornerInsertionInput`, with `ε₀ = 3` and `ρ₀ = 1`.  The insertion is proved
(`GloballyDistinguishedSectionFamily.separatedCornerInsertionInput`), so `osinLemma94CaseTwoInput`
is closed.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

namespace CaseTwoWalk

/-- Rotating by the length of the front piece swaps the two pieces. -/
theorem rotate_add_length_of_eq {α : Type*} {l front back : List α} {r : ℕ}
    (h : l.rotate r = front ++ back) : l.rotate (r + front.length) = back ++ front := by
  rw [← List.rotate_rotate, h, List.rotate_append_length_eq]

/-- A property that holds at the last entry of a list, and passes from each entry to the one
before it, holds at every entry. -/
theorem getElem_of_last_of_step {α : Type*} {Q : α → Prop} {l : List α}
    (hstep : ∀ (i : ℕ) (hi : i + 1 < l.length), Q l[i + 1] → Q l[i])
    (hlast : ∀ (i : ℕ) (hi : i < l.length), i + 1 = l.length → Q l[i]) :
    ∀ (i : ℕ) (hi : i < l.length), Q l[i] := by
  intro i hi
  obtain ⟨n, hn⟩ : ∃ n, l.length = i + 1 + n := ⟨l.length - (i + 1), by omega⟩
  induction n generalizing i with
  | zero => exact hlast i hi (by omega)
  | succ n ih => exact hstep i (by omega) (ih (i + 1) (by omega) (by omega))

section Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The walk does not jump over a piece.**  If the walk of a face reads `front ++ back ++ rest`
from some base, with `back` nonempty, then the walk steps from a dart of `front` to a dart of
`front` or of `back`. -/
theorem facePerm_mem_front_of_not_mem_back {f : S.diagram.toCombMap.Face} {r : ℕ}
    {front back rest : List S.diagram.toCombMap.Dart}
    (hwalk : (S.diagram.faceBoundary f).darts.rotate r = front ++ back ++ rest)
    (hback : back ≠ []) {x : S.diagram.toCombMap.Dart} (hx : x ∈ front)
    (hnot : S.diagram.toCombMap.facePerm x ∉ back) : S.diagram.toCombMap.facePerm x ∈ front := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlen : p + 1 < (front ++ back).length := by
    have hpos : back.length ≠ 0 := fun h => hback (List.eq_nil_of_length_eq_zero h)
    rw [List.length_append]
    omega
  have hstep := GloballyDistinguishedSectionFamily.facePerm_getElem_of_rotate_eq hwalk p hlen
  rw [List.getElem_append_left hp] at hstep
  rw [hstep]
  by_cases hin : p + 1 < front.length
  · rw [List.getElem_append_left hin]
    exact List.getElem_mem hin
  · have hge : front.length ≤ p + 1 := by omega
    refine absurd ?_ hnot
    rw [hstep, List.getElem_append_right hge]
    exact List.getElem_mem _

/-- A window of a cutting side runs back across. -/
theorem runsBackAcross_window (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {t : ℕ}
    (ht : t < P.sideCount k) (hcut : P.kind k t = .cutting) (b' n : ℕ) :
    S.RunsBackAcross (((P.sideDarts k t).drop b').take n) := by
  intro j e e' he he'
  have hlt : j + 1 < n := by
    by_contra hge
    have hle : n ≤ j + 1 := by omega
    rw [List.getElem?_take_eq_none hle] at he'
    simp at he'
  rw [List.getElem?_take_of_lt (show j < n by omega), List.getElem?_drop] at he
  rw [List.getElem?_take_of_lt hlt, List.getElem?_drop, ← Nat.add_assoc] at he'
  exact P.cutting_interior k t ht hcut (b' + j) e e' he he'

end Diagram

end CaseTwoWalk

open CaseTwoWalk

/-- **One backwards connector pair of Case 2.**  Once `ε ≥ 3`, a dart-minimal family has no
backwards connector pair of polygon `k` whose target side is a cutting path. -/
theorem osinLemma94CaseTwo_false
    (hinsert : GloballyDistinguishedSectionFamily.SeparatedCornerInsertionInput.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} (heps : 3 ≤ eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    (hback : C.b' < C.b) (hcut : P.kind k C.target = .cutting) : False := by
  obtain ⟨N⟩ := C.exists_nonempty_connectors (symmetricLabelAlphabet.symmetric D) (by omega)
  have hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ≠ P.face k := by
    intro cell hcell
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hcell
    exact P.face_not_cell k j
  have hf : S.UnselectedGFace (P.face k) := ⟨P.face_ne_outer k, hcells, P.face_unselected k⟩
  obtain ⟨jcell, hsource⟩ : ∃ j, P.kind k C.source = .cell j := C.source_mem
  obtain ⟨arc, harc⟩ := P.cell_arc k C.source jcell C.source_lt hsource
  have hfwd := C.source_forward
  have ha' : C.a' ≤ (P.sideDarts k C.source).length := by
    rw [← CaseOneWalk.polygon_length_word P k C.source]
    exact C.a'_le
  have hb : C.b ≤ (P.sideDarts k C.target).length := by
    rw [← CaseOneWalk.polygon_length_word P k C.target]
    exact C.b_le
  -- The target segment is longer than `ε`.
  have hlong : eps < C.b - C.b' := by
    have h1 := C.target_long
    rw [WordMetric.wordDist_comm (symmetricLabelAlphabet D).alphabet.symmetricGenerating] at h1
    exact lt_of_lt_of_le h1 (OsinComponents.wordDist_vertex_le' (symmetricLabelAlphabet D)
      (w := P.word k C.target) C.target_admissible (P.corner k C.target) hback.le C.b_le)
  obtain ⟨X, Y, r, hwalk, hX, hY⟩ := CaseOneWalk.polygon_four_windows P k C.source_lt
    C.target_lt C.distinct hfwd.le ha' hback.le hb
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = ((P.sideDarts k C.target).drop C.b').take (C.b - C.b') :=
    ⟨_, rfl⟩
  obtain ⟨Sw, hSw⟩ : ∃ Sw, Sw = ((P.sideDarts k C.source).drop C.a).take (C.a' - C.a) :=
    ⟨_, rfl⟩
  rw [← hTw, ← hSw] at hwalk
  have hTwlen : Tw.length = C.b - C.b' := by
    rw [hTw, List.length_take, List.length_drop]
    omega
  have hTwne : Tw ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hSwne : Sw ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [hSw, List.length_take, List.length_drop]
    omega
  have hTwt : ∀ d ∈ Tw, d ∈ P.sideDarts k C.target := by
    intro d hd
    rw [hTw] at hd
    exact List.mem_of_mem_drop (List.mem_of_mem_take hd)
  have hSws : ∀ d ∈ Sw, d ∈ P.sideDarts k C.source := by
    intro d hd
    rw [hSw] at hd
    exact List.mem_of_mem_drop (List.mem_of_mem_take hd)
  have hruns : S.RunsBackAcross Tw := by
    rw [hTw]
    exact runsBackAcross_window P k C.target_lt hcut _ _
  -- The walk from four bases.
  have hwalkXT : (S.diagram.faceBoundary (P.face k)).darts.rotate r = X ++ Tw ++ (Y ++ Sw) := by
    rw [hwalk]
    simp only [List.append_assoc]
  have hwalkX : (S.diagram.faceBoundary (P.face k)).darts.rotate r = X ++ (Tw ++ (Y ++ Sw)) := by
    rw [hwalk]
    simp only [List.append_assoc]
  have hwalkT : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + X.length) =
      Tw ++ (Y ++ (Sw ++ X)) := by
    rw [rotate_add_length_of_eq hwalkX]
    simp only [List.append_assoc]
  have hwalkYS : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + (X ++ Tw).length) =
      Y ++ Sw ++ (X ++ Tw) := rotate_add_length_of_eq hwalkXT
  have hwalkY : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + (X ++ Tw).length) =
      Y ++ (Sw ++ X ++ Tw) := by
    rw [hwalkYS]
    simp only [List.append_assoc]
  -- Where the reverse darts of the target segment lie.
  have hTwface : ∀ d ∈ Tw, S.diagram.toCombMap.faceOf d = P.face k := by
    intro d hd
    have hmem : d ∈ (S.diagram.faceBoundary (P.face k)).darts.rotate r := by
      rw [hwalk]
      simp [hd]
    exact ((S.diagram.faceBoundary (P.face k)).mem_iff _).mp (List.mem_rotate.mp hmem)
  have hnotT : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∉ Tw :=
    GloballyDistinguishedSectionFamily.alpha_not_mem_of_dartMinimal
      GloballyDistinguishedSectionFamily.pendantPathRemovalInput hS hf hwalkT hruns
  have hnotS : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∉ Sw := by
    intro d hd h
    have hz : S.diagram.toCombMap.alpha d ∈ arc.reverseDarts := by
      rw [← harc]
      exact hSws _ h
    refine GFaceWordInsertion.faceOf_alpha_ne_of_mem_reverseDarts S.diagram hcells jcell arc hz ?_
    rw [S.diagram.toCombMap.alpha_involutive d]
    exact hTwface d hd
  have hXY : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∈ X ∨ S.diagram.toCombMap.alpha d ∈ Y := by
    intro d hd
    have hmem : S.diagram.toCombMap.alpha d ∈
        (S.diagram.faceBoundary (P.face k)).darts.rotate r :=
      List.mem_rotate.mpr (((S.diagram.faceBoundary (P.face k)).mem_iff _).mpr
        (P.cutting_internal k C.target C.target_lt hcut d (hTwt d hd)))
    rw [hwalk] at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact Or.inl h
    · exact absurd h (hnotT d hd)
    · exact Or.inr h
    · exact absurd h (hnotS d hd)
  have hstep : ∀ (i : ℕ) (hi : i + 1 < Tw.length),
      S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha Tw[i + 1]) =
        S.diagram.toCombMap.alpha Tw[i] := by
    intro i hi
    have hi' : i < Tw.length := by omega
    exact hruns i _ _ (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hi)
  have hlastlt : Tw.length - 1 < Tw.length := by omega
  have hval1 : RelLetter.listVal N.endWord = RelLetter.listVal (dartWord S.diagram X) :=
    N.end_value.trans (mul_left_cancel (C.end_geodesic.2.1.trans hX.symm))
  have hval2 : RelLetter.listVal N.startWord = RelLetter.listVal (dartWord S.diagram Y) :=
    N.start_value.trans (mul_left_cancel (C.start_geodesic.2.1.trans hY.symm))
  rcases hXY _ (List.getElem_mem hlastlt) with hlX | hlY
  · -- The reverse darts all lie in `X`: insert the end connector across the face.
    have hallX : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∈ X := by
      have hstepX : ∀ (i : ℕ) (hi : i + 1 < Tw.length),
          S.diagram.toCombMap.alpha Tw[i + 1] ∈ X → S.diagram.toCombMap.alpha Tw[i] ∈ X := by
        intro i hi hx
        have hi' : i < Tw.length := by omega
        have h := facePerm_mem_front_of_not_mem_back hwalkXT hTwne hx
          (by rw [hstep i hi]; exact hnotT _ (List.getElem_mem hi'))
        rwa [hstep i hi] at h
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      refine getElem_of_last_of_step (Q := fun d => S.diagram.toCombMap.alpha d ∈ X) (l := Tw)
        hstepX ?_ i hi
      intro j hj hjl
      obtain rfl : j = Tw.length - 1 := by omega
      exact hlX
    obtain ⟨T, hTsum, hTcount, path', hlen', hnodup, hjoints, first, second, hfs, hfirst, hsecond,
      hsides⟩ := hinsert S (P.face k) r X (Tw ++ (Y ++ Sw)) Tw N.endWord hf hwalkX
        (by simp [hTwne]) (List.prefix_append _ _).isInfix hallX hruns N.end_nonempty
        N.end_admissible hval1
    obtain ⟨U, hUsum, hUcount⟩ :=
      GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant
        GloballyDistinguishedSectionFamily.pendantPathRemovalInput T path' first second
        (List.ne_nil_of_length_pos (by omega)) hnodup hfs hfirst hsecond hjoints hsides
    have hle := hS U (hUsum.trans hTsum)
    have hshort := N.end_short
    omega
  · -- The reverse darts all lie in `Y`: insert the start connector across the face.
    have hallY : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∈ Y := by
      have hstepY : ∀ (i : ℕ) (hi : i + 1 < Tw.length),
          S.diagram.toCombMap.alpha Tw[i + 1] ∈ Y → S.diagram.toCombMap.alpha Tw[i] ∈ Y := by
        intro i hi hy
        have hi' : i < Tw.length := by omega
        have h := facePerm_mem_front_of_not_mem_back hwalkYS hSwne hy
          (by rw [hstep i hi]; exact hnotS _ (List.getElem_mem hi'))
        rwa [hstep i hi] at h
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      refine getElem_of_last_of_step (Q := fun d => S.diagram.toCombMap.alpha d ∈ Y) (l := Tw)
        hstepY ?_ i hi
      intro j hj hjl
      obtain rfl : j = Tw.length - 1 := by omega
      exact hlY
    obtain ⟨T, hTsum, hTcount, path', hlen', hnodup, hjoints, first, second, hfs, hfirst, hsecond,
      hsides⟩ := hinsert S (P.face k) (r + (X ++ Tw).length) Y (Sw ++ X ++ Tw) Tw N.startWord
        hf hwalkY (by simp [hSwne]) (List.suffix_append _ _).isInfix hallY hruns
        N.start_nonempty N.start_admissible hval2
    obtain ⟨U, hUsum, hUcount⟩ :=
      GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant
        GloballyDistinguishedSectionFamily.pendantPathRemovalInput T path' first second
        (List.ne_nil_of_length_pos (by omega)) hnodup hfs hfirst hsecond hjoints hsides
    have hle := hS U (hUsum.trans hTsum)
    have hshort := N.start_short
    omega

/-- **Case 2 of Lemma 9.4 from the separated insertion.**  The thresholds are `ε₀ = 3` and
`ρ₀ = 1`. -/
theorem osinLemma94CaseTwoInput_of_insertion
    (hinsert : GloballyDistinguishedSectionFamily.SeparatedCornerInsertionInput.{u, w, v}) :
    OsinLemma94CaseTwoInput.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu _ _ _ _ _
  refine ⟨3, fun eps heps => ⟨1, Nat.one_pos, ?_⟩⟩
  intro rho _ W _ Delta cuts _ _ S _ hS P _ k C hback hcut
  exact osinLemma94CaseTwo_false hinsert heps hS P k C hback hcut

/-- **Case 2 of Lemma 9.4.**  "Case 2 … This contradicts our assumption that `∑ l(t_i)` is
minimal."  A backwards connector pair (39) from an (A1) side to a cutting side shortens the
cutting path, against `DartMinimal`. -/
theorem osinLemma94CaseTwoInput : OsinLemma94CaseTwoInput.{u, w, v} :=
  osinLemma94CaseTwoInput_of_insertion
    GloballyDistinguishedSectionFamily.separatedCornerInsertionInput

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CaseTwoWalk.rotate_add_length_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CaseTwoWalk.getElem_of_last_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.CaseTwoWalk.facePerm_mem_front_of_not_mem_back
#audit_axioms GroupApproximation.GGT.VanKampen.CaseTwoWalk.runsBackAcross_window
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseTwo_false
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseTwoInput_of_insertion
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseTwoInput
