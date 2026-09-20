import GroupApproximation.Manuscript.NonMF.Full.GL01.Bridge
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.HullSCLemma44RelativeDehn
import GroupApproximation.Meta.AxiomGuard

/-!
# GL01: the triangle corner, and the corner exclusion

*GL01 copy.*  This re-proves the foreign module `GreendlingerLeaf.P01EmptyTwoGon.TriangleCorner`
(origin/main blob `81ae207fb`).  That module imports `TouchCornerSwitch`, which is last changed by a
commit marked WIP, so it is not imported.  The endpoint `touchCornerStatement` is assembled here
from `GL01.Switch`, `GL01.Bridge` and the triangle corner.

Infrastructure for `thm:hull` in non_mf_groups_exist.tex, through Osin, arXiv:math/0411039v3,
§9, proof of Lemma 9.4.  It certifies no printed sentence on its own.

Notation: `M = S.diagram.toCombMap`, `φ = M.facePerm`, `α = M.alpha`, `F = P.face k`.

`OneCornerExcluded P` holds for every polygon system of a globally distinguished section family
with `ε ≥ 2` (`oneCornerExcluded`).  Let `d` be a dart of `F` with `α d` on `A = objectFace o` and
`α (φ d)` on `B = objectFace o′`, where `o ≠ o′`.
1. `φ d ≠ d`, since otherwise `o = o′`.  So a rotation of the walk of `F` reads `d, φ d, L`
   (`exists_rotate_corner`).
2. `F` is no relator cell, so its word has value `1`, and `L` has value `y⁻¹ x⁻¹`, where `x`, `y`
   are the labels of `d` and `φ d`.
3. The words `[x, x⁻¹]` and `[y⁻¹, x⁻¹]` are legal connectors of length and norm at most `2 ≤ ε`
   (`TriangleConnector`).
4. One of `o`, `o′` is a cell.  The walk of `F` is a quadrilateral with single-dart arcs, and
   `RealizedSectionFamily.false_of_quadrilateral_face` contradicts the weight maximality of `S`
   (`false_of_triangle_walk`).

With `switchCornerExcluded_of_one` and `cornerExcluded_of_switch` this gives
`touchCornerStatement : TouchCornerStatement`, with thresholds `ε₀ = 2` and `ρ₀ = 1`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

section TriangleCornerLists

/-- A dart of a cycle is a cyclic arc of length one. -/
theorem exists_singleArc {Dart : Type v} {cycle : List Dart} {a : Dart} (ha : a ∈ cycle) :
    ∃ arc : CyclicArc cycle, arc.darts = [a] ∧ arc.length = 1 ∧ arc.start.1 < cycle.length := by
  obtain ⟨n, hn, hna⟩ := List.getElem_of_mem ha
  have e : cycle.drop n ++ cycle.take n = a :: (cycle.drop (n + 1) ++ cycle.take n) := by
    rw [List.drop_eq_getElem_cons hn, hna, List.cons_append]
  exact ⟨⟨⟨n, by omega⟩, 1, by omega⟩, (congrArg (List.take 1) e).trans rfl, rfl, hn⟩

/-- A cyclic arc on the single dart `α a` has the reversed boundary `[a]`. -/
theorem reverseDarts_eq_singleton {M : CombMap} {cycle : List M.Dart} (arc : CyclicArc cycle)
    {a : M.Dart} (h : arc.darts = [M.alpha a]) : arc.reverseDarts = [a] := by
  rw [CyclicArc.reverseDarts, h]
  exact congrArg (fun z => [z]) (M.alpha_involutive a)

/-- Rotating one step further moves the head to the end. -/
theorem rotate_succ_of_rotate_eq {α : Type*} {l : List α} {r : ℕ} {a : α} {tl : List α}
    (h : l.rotate r = a :: tl) : l.rotate (r + 1) = tl ++ [a] := by
  have e : (a :: tl).rotate 1 = tl ++ [a] := by
    have h1 := List.rotate_cons_succ tl a 0
    rwa [List.rotate_zero] at h1
  rw [← List.rotate_rotate, h, e]

/-- A position of the boundary word lies inside one section. -/
theorem exists_section_of_lt {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {lambda c : ℝ} {word : List (RelLetter G Lambda)} (cs : SectionCuts D lambda c word) {p : ℕ}
    (hp : p < word.length) :
    ∃ j : Fin cs.count, cs.cut j.castSucc ≤ p ∧ p + 1 ≤ cs.cut j.succ := by
  classical
  have hex : ∃ n : ℕ, ∃ h : n < cs.count + 1, p < cs.cut ⟨n, h⟩ :=
    ⟨cs.count, Nat.lt_succ_self _, lt_of_lt_of_eq hp cs.cut_last.symm⟩
  obtain ⟨hn, hpn⟩ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have e : (⟨Nat.find hex, hn⟩ : Fin (cs.count + 1)) = 0 := Fin.ext h0
    rw [e, cs.cut_zero] at hpn
    exact Nat.not_lt_zero _ hpn
  have hlt : Nat.find hex - 1 < cs.count := by omega
  refine ⟨⟨Nat.find hex - 1, hlt⟩, ?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨by omega, hcon⟩
  · have hsucc : (⟨Nat.find hex - 1, hlt⟩ : Fin cs.count).succ = ⟨Nat.find hex, hn⟩ :=
      Fin.ext (by show Nat.find hex - 1 + 1 = Nat.find hex; omega)
    rw [hsucc]
    exact hpn

/-- **A corner of a face walk.**  A dart `d` of a face with `φ d ≠ d` starts a rotation of the
walk that reads `d, φ d, …`. -/
theorem exists_rotate_corner {M : CombMap} {f : M.Face} (B : FaceBoundary M f) {d : M.Dart}
    (hd : d ∈ B.darts) (hfix : M.facePerm d ≠ d) :
    ∃ (r : ℕ) (L : List M.Dart), r ≤ B.darts.length ∧
      B.darts.rotate r = d :: M.facePerm d :: L := by
  obtain ⟨n, hn, hnd⟩ := List.getElem_of_mem hd
  have hrot : B.darts.rotate n = d :: (B.darts.drop (n + 1) ++ B.darts.take n) := by
    rw [List.rotate_eq_drop_append_take hn.le, List.drop_eq_getElem_cons hn, hnd, List.cons_append]
  have key : ∀ (l T : List M.Dart), l = d :: T → l.IsChain (fun x y => M.facePerm x = y) →
      (∀ h : l ≠ [], M.facePerm (l.getLast h) = l.head h) → ∃ L, l = d :: M.facePerm d :: L := by
    rintro l T rfl hch hcl
    cases T with
    | nil => exact absurd (hcl (List.cons_ne_nil _ _)) hfix
    | cons e L =>
      have h1 : M.facePerm d = e := (List.isChain_cons_cons.mp hch).1
      exact ⟨L, congrArg (fun z => d :: z :: L) h1.symm⟩
  obtain ⟨L, hL⟩ := key _ _ hrot
    (Embedded.isChain_rotate_of_isChain_closes B.nonempty B.chain B.closes n)
    (Embedded.isChain_rotate_closing B.nonempty B.chain B.closes n)
  exact ⟨n, L, hn.le, hL⟩

end TriangleCornerLists

section TriangleCornerConnectors

/-- A nonempty legal word of length and norm at most `ε` with value `g`, whose letters have legal
inverses: the connector input of `RealizedSectionFamily.false_of_quadrilateral_face`. -/
def TriangleConnector {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (g : G) : Prop :=
  ∃ s : List (RelLetter G Lambda), s ≠ [] ∧
    HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s ∧
    (∀ l ∈ s, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l)) ∧
    RelLetter.listVal s = g ∧ s.length ≤ eps ∧
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s) ≤ eps

/-- Two legal letters give a connector for the product of their values. -/
theorem triangleConnector_pair {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {eps : ℕ} (heps : 2 ≤ eps) {p q : RelLetter G Lambda}
    (hp : (symmetricLabelAlphabet D).IsLetter p) (hq : (symmetricLabelAlphabet D).IsLetter q) :
    TriangleConnector D eps (p.val * q.val) := by
  have hsymm := symmetricLabelAlphabet.symmetric D
  have hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) [p, q] := by
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact hp
    · rcases List.mem_cons.mp hl' with rfl | hl''
      · exact hq
      · simp at hl''
  have hval : RelLetter.listVal [p, q] = p.val * q.val := by
    simp only [RelLetter.listVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
  have hnorm := HullSC.RelativeBoundaryContiguity.wordNorm_listVal_le_length
    (symmetricLabelAlphabet D) [p, q] hadm
  rw [symmetricLabelAlphabet.wordNorm_eq] at hnorm
  exact ⟨[p, q], List.cons_ne_nil _ _, hadm,
    fun l hl => HullSC.isLetter_relWordInv _ hsymm (hadm l hl), hval, heps,
    le_trans hnorm heps⟩

/-- A legal letter and its inverse give a connector for `1`. -/
theorem triangleConnector_one {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {eps : ℕ} (heps : 2 ≤ eps) {p : RelLetter G Lambda}
    (hp : (symmetricLabelAlphabet D).IsLetter p) : TriangleConnector D eps 1 := by
  have h := triangleConnector_pair heps hp
    (HullSC.isLetter_relWordInv _ (symmetricLabelAlphabet.symmetric D) hp)
  rwa [HullSC.RelWord.val_inv, mul_inv_cancel] at h

/-- Two legal letters give a connector for the product of the inverses of their values. -/
theorem triangleConnector_inv {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {eps : ℕ} (heps : 2 ≤ eps) {p q : RelLetter G Lambda}
    (hp : (symmetricLabelAlphabet D).IsLetter p) (hq : (symmetricLabelAlphabet D).IsLetter q) :
    TriangleConnector D eps (p.val⁻¹ * q.val⁻¹) := by
  have hsymm := symmetricLabelAlphabet.symmetric D
  have h := triangleConnector_pair heps (HullSC.isLetter_relWordInv _ hsymm hp)
    (HullSC.isLetter_relWordInv _ hsymm hq)
  rwa [HullSC.RelWord.val_inv, HullSC.RelWord.val_inv] at h

end TriangleCornerConnectors

section TriangleCornerWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **A quadrilateral walk with single-dart arcs.**  A rotation `X, t, Y, s` of the walk of a
polygon face, with `α s` on cell `i`, `α t` on another object `o′`, and connectors for `X` and
`Y`, contradicts the weight maximality of `S`. -/
theorem false_of_triangle_walk (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    {s t : S.diagram.toCombMap.Dart} {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r = X ++ [t] ++ Y ++ [s])
    (i : Fin S.diagram.rCellCount)
    (hs : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha s) =
      OsinLemma94RealizedPolygons.objectFace S (some i))
    (o' : Option (Fin S.diagram.rCellCount)) (ho' : o' ≠ some i)
    (ht : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha t) =
      OsinLemma94RealizedPolygons.objectFace S o')
    (hX : TriangleConnector D eps (RelLetter.listVal (dartWord S.diagram X)))
    (hY : TriangleConnector D eps (RelLetter.listVal (dartWord S.diagram Y))) : False := by
  obtain ⟨s1, hne1, hadm1, hinv1, hval1, hlen1, hnorm1⟩ := hX
  obtain ⟨s2, hne2, hadm2, hinv2, hval2, hlen2, hnorm2⟩ := hY
  have hsmem : S.diagram.toCombMap.alpha s ∈ cellDarts S.diagram i :=
    ((S.diagram.faceBoundary (cell S.diagram i).face).mem_iff _).mpr hs
  obtain ⟨sarc, hsd, hsl, -⟩ := exists_singleArc hsmem
  have hsrev : sarc.reverseDarts = [s] := reverseDarts_eq_singleton sarc hsd
  cases o' with
  | some j =>
    have htmem : S.diagram.toCombMap.alpha t ∈ targetDarts S.diagram (some j) :=
      ((S.diagram.faceBoundary (cell S.diagram j).face).mem_iff _).mpr ht
    obtain ⟨tarc, htd, htl, -⟩ := exists_singleArc htmem
    have htrev : targetBoundaryDarts S.diagram (some j) tarc = [t] :=
      reverseDarts_eq_singleton tarc htd
    exact RealizedSectionFamily.false_of_quadrilateral_face S.toRealizedSectionFamily
      S.label_admissible S.weight_maximal (P.face k) (P.face_ne_outer k) (relatorCell_face_ne P k)
      (P.face_unselected k) i (some j) sarc tarc X Y r
      (htrav.trans (congrArg₂ (fun (A B : List S.diagram.toCombMap.Dart) => X ++ A ++ Y ++ B)
        htrev.symm hsrev.symm))
      (lt_of_lt_of_eq Nat.one_pos hsl.symm) (lt_of_lt_of_eq Nat.one_pos htl.symm)
      (fun h => absurd h (Option.some_ne_none j)) ho'
      s1 s2 hne1 hne2 hadm1 hinv1 hadm2 hinv2 hval1 hval2 hlen1 hlen2 hnorm1 hnorm2
  | none =>
    have htmem : t ∈ targetDarts S.diagram none := by
      show t ∈ (S.diagram.faceBoundary S.diagram.outerFace).darts.reverse.map
        S.diagram.toCombMap.alpha
      exact List.mem_map.mpr ⟨S.diagram.toCombMap.alpha t,
        List.mem_reverse.mpr (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff _).mpr ht),
        S.diagram.toCombMap.alpha_involutive t⟩
    obtain ⟨tarc, htd, htl, hts⟩ := exists_singleArc htmem
    have htb : targetBoundaryDarts S.diagram none tarc = [t] := htd
    have hcyc : (targetDarts S.diagram none).length = Delta.boundaryWord.length := by
      have e := congrArg List.length (dartWord_outerDarts S.diagram)
      rw [S.equiv.boundaryWord_eq, dartWord, List.length_map] at e
      exact e
    obtain ⟨j, hj1, hj2⟩ := exists_section_of_lt cuts (lt_of_lt_of_eq hts hcyc)
    exact RealizedSectionFamily.false_of_quadrilateral_face S.toRealizedSectionFamily
      S.label_admissible S.weight_maximal (P.face k) (P.face_ne_outer k) (relatorCell_face_ne P k)
      (P.face_unselected k) i none sarc tarc X Y r
      (htrav.trans (congrArg₂ (fun (A B : List S.diagram.toCombMap.Dart) => X ++ A ++ Y ++ B)
        htb.symm hsrev.symm))
      (lt_of_lt_of_eq Nat.one_pos hsl.symm) (lt_of_lt_of_eq Nat.one_pos htl.symm)
      (fun _ => ⟨j, hj1, by rw [htl]; exact hj2⟩)
      (Option.some_ne_none i).symm
      s1 s2 hne1 hne2 hadm1 hinv1 hadm2 hinv2 hval1 hval2 hlen1 hlen2 hnorm1 hnorm2

/-- **The corner walk.**  A rotation `x, y, L` of the walk of a polygon face with different
objects `o ≠ o′` across `x` and `y` contradicts the weight maximality of `S`, once `ε ≥ 2`. -/
theorem false_of_corner_rotate (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (heps : 2 ≤ eps) {x y : S.diagram.toCombMap.Dart} {L : List S.diagram.toCombMap.Dart} {r : ℕ}
    (hr : r ≤ (S.diagram.faceBoundary (P.face k)).darts.length)
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r = x :: y :: L)
    {o o' : Option (Fin S.diagram.rCellCount)} (hoo : o ≠ o')
    (hx : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) =
      OsinLemma94RealizedPolygons.objectFace S o)
    (hy : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) =
      OsinLemma94RealizedPolygons.objectFace S o') : False := by
  have hlx : (symmetricLabelAlphabet D).IsLetter (S.diagram.label x) := S.label_admissible x
  have hly : (symmetricLabelAlphabet D).IsLetter (S.diagram.label y) := S.label_admissible y
  have hface : RelLetter.listVal (S.diagram.faceWord (P.face k)) = 1 := by
    rcases S.diagram.inner_face (P.face k) (P.face_ne_outer k) with ⟨C, hC, hC'⟩ | h
    · exact absurd hC' (relatorCell_face_ne P k C hC)
    · exact h
  have hlen : r ≤ (S.diagram.faceWord (P.face k)).length := by
    rw [DiscDiagram.faceWord, List.length_map]
    exact hr
  have h0 := HullSC.RelWord.listVal_rotate _ hlen
  rw [hface, mul_one, inv_mul_cancel, DiscDiagram.faceWord, ← List.map_rotate, htrav] at h0
  have h1 : (S.diagram.label x).val * ((S.diagram.label y).val *
      RelLetter.listVal (dartWord S.diagram L)) = 1 := by
    simpa only [dartWord, RelLetter.listVal, List.map_cons, List.prod_cons] using h0
  have h2 : (S.diagram.label x).val * (S.diagram.label y).val *
      RelLetter.listVal (dartWord S.diagram L) = 1 := by
    rw [mul_assoc]
    exact h1
  have hL : RelLetter.listVal (dartWord S.diagram L) =
      (S.diagram.label y).val⁻¹ * (S.diagram.label x).val⁻¹ := by
    rw [← mul_inv_rev]
    exact eq_inv_of_mul_eq_one_right h2
  have hA : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + 1) = y :: (L ++ [x]) :=
    rotate_succ_of_rotate_eq htrav
  have hB : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + 1 + 1) = L ++ [x] ++ [y] :=
    rotate_succ_of_rotate_eq hA
  have hone : TriangleConnector D eps
      (RelLetter.listVal (dartWord S.diagram ([] : List S.diagram.toCombMap.Dart))) :=
    triangleConnector_one heps hlx
  have hpair : TriangleConnector D eps (RelLetter.listVal (dartWord S.diagram L)) := by
    rw [hL]
    exact triangleConnector_inv heps hly hlx
  cases o with
  | some i =>
    exact false_of_triangle_walk P k (s := x) (t := y) (X := []) (Y := L) (r := r + 1)
      (hA.trans (by simp)) i hx o' (fun h => hoo h.symm) hy hone hpair
  | none =>
    cases o' with
    | none => exact hoo rfl
    | some j =>
      exact false_of_triangle_walk P k (s := y) (t := x) (X := L) (Y := []) (r := r + 1 + 1)
        (hB.trans (by simp)) j hy none (Option.some_ne_none j).symm hx hpair hone

/-- **The triangle corner is excluded**: a dart `d` of a polygon face with different objects across
`d` and `φ d` contradicts the weight maximality of `S`, once `ε ≥ 2`. -/
theorem false_of_corner (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (heps : 2 ≤ eps)
    {o o' : Option (Fin S.diagram.rCellCount)} (hoo : o ≠ o') {d : S.diagram.toCombMap.Dart}
    (hd : S.diagram.toCombMap.faceOf d = P.face k)
    (hx : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) =
      OsinLemma94RealizedPolygons.objectFace S o)
    (hy : S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (S.diagram.toCombMap.facePerm d)) =
      OsinLemma94RealizedPolygons.objectFace S o') : False := by
  have hfix : S.diagram.toCombMap.facePerm d ≠ d := by
    intro h
    rw [h] at hy
    exact hoo (OsinLemma94RealizedPolygons.objectFace_injective S (hx.symm.trans hy))
  obtain ⟨r, L, hr, htrav⟩ := exists_rotate_corner (S.diagram.faceBoundary (P.face k))
    (((S.diagram.faceBoundary (P.face k)).mem_iff d).mpr hd) hfix
  exact false_of_corner_rotate P k heps hr htrav hoo hx hy

end TriangleCornerWalk

section CornerEndpoint

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The triangle corner exclusion** for every polygon system, once `ε ≥ 2`. -/
theorem oneCornerExcluded (P : OsinLemma94RealizedPolygons S) (heps : 2 ≤ eps) :
    OneCornerExcluded P := by
  intro k _ _ _ _ hoo _ hd hx hy _ _
  exact false_of_corner P k heps hoo hd hx hy

/-- **The corner exclusion** for a dart-minimal family, once `ε ≥ 2`. -/
theorem cornerExcluded (P : OsinLemma94RealizedPolygons S) (hS : S.DartMinimal)
    (heps : 2 ≤ eps) : CornerExcluded P :=
  cornerExcluded_of_switch P hS (switchCornerExcluded_of_one P hS (oneCornerExcluded P heps))

end CornerEndpoint

/-- **The corner exclusion** `TouchCornerStatement` (module `TouchTwoGon`), with `ε₀ = 2` and
`ρ₀ = 1`: a maximal polygon system of a dart-minimal globally distinguished section family has no
corner configuration. -/
theorem touchCornerStatement : TouchCornerStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨2, fun _ heps => ⟨1, Nat.one_pos, ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ hminimal P _
  exact cornerExcluded P hminimal heps

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.false_of_triangle_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.false_of_corner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.oneCornerExcluded
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.touchCornerStatement
