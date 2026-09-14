import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellValue
import GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# The innermost lobe of the pinched carrier part: its arc, its simplicity and its side

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`: some rotation of the
face walk of `f` reads `X q⁻¹ Y p⁻¹`, some rotation of the carrier of `Π` reads `q B p A`, and the
exterior face is off the side of the pocket walk `invDarts X ++ invDarts B`.  Let
`invDarts B = l₁ ++ L ++ l₂` with `L` a closed dart walk repeating no vertex (the innermost lobe of
`OsinLemma94CaseOneCellLobeValueStatement`).  This module supplies the inputs of the walk-level
loop-cut kill `SameCellSimplePocket.false_of_simpleWalk_of_below` for `L`.

* `exists_arc_of_lobe`: `L = [] ++ invDarts T` for an arc `T` of `Π`.
* `isSimpleClosedWalk_lobe`: `L` is simple when it reads an element other than `1`.  From length
  three this is `ClosedWalkInnermostLobe.isSimpleClosedWalk_of_nodup`; a lobe of length one is a
  loop, and a lobe of length two with a dart and its reverse is a hair, which reads `1`.
* `cell_not_mem_sideFaces_lobe`: `Π` is off the side of `L`, since every dart of `L` has `Π` across.
* `outerFace_not_mem_sideFaces_lobe`: the exterior face is off the side of `L`.  The face class of
  `L` never meets an edge of the pocket walk off `L`: such an edge has `f` or `Π` across, and `f`
  reaches `Π` through the first dart of `p`, which is not an edge of `L`.  So the side of `L` lies
  in the side of the pocket walk (`sideFaces_subset_of_agree`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace SameCellCellLobe

/-- **Two keep predicates that agree along a face class give the same class.**  If every dart in
the class of `d` that `keep'` retains is retained by `keep`, every chain of steps under `keep`
from `d` is a chain under `keep'`. -/
theorem eqvGen_faceClass_of_agree {M : CombMap.{v}} {keep keep' : M.Dart → Prop} {d x : M.Dart}
    (hagree : ∀ y, Relation.EqvGen (CombMap.FaceClassStep M keep) d y → keep' y → keep y)
    (h : Relation.EqvGen (CombMap.FaceClassStep M keep) d x) :
    Relation.EqvGen (CombMap.FaceClassStep M keep') d x := by
  have key : ∀ y z, Relation.EqvGen (CombMap.FaceClassStep M keep) y z →
      Relation.EqvGen (CombMap.FaceClassStep M keep) d y →
        Relation.EqvGen (CombMap.FaceClassStep M keep') y z := by
    intro y z hyz
    induction hyz with
    | rel _ _ hab =>
        intro hda
        refine Relation.EqvGen.rel _ _ ?_
        rcases hab with hb | ⟨hnot, hb⟩
        · exact Or.inl hb
        · exact Or.inr ⟨fun hk => hnot (hagree _ hda hk), hb⟩
    | refl _ =>
        intro _
        exact Relation.EqvGen.refl _
    | symm _ _ hab ih =>
        intro hdb
        exact Relation.EqvGen.symm _ _
          (ih (Relation.EqvGen.trans _ _ _ hdb (Relation.EqvGen.symm _ _ hab)))
    | trans _ _ _ hab _ ih₁ ih₂ =>
        intro hda
        exact Relation.EqvGen.trans _ _ _ (ih₁ hda) (ih₂ (Relation.EqvGen.trans _ _ _ hda hab))
  exact key d x h (Relation.EqvGen.refl d)

/-- **The side of a sub-walk lies in the side of the walk** when the face classes of the sub-walk
meet no edge of the walk that is not an edge of the sub-walk. -/
theorem sideFaces_subset_of_agree {M : CombMap.{v}} {L w : List M.Dart}
    (hsub : ∀ d ∈ L, d ∈ w)
    (hagree : ∀ d ∈ L, ∀ y, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M L)) d y →
      walkKeep M w y → walkKeep M L y) :
    sideFaces M L ⊆ sideFaces M w := by
  classical
  intro F hF
  unfold sideFaces at hF ⊢
  rw [Finset.mem_filter] at hF ⊢
  obtain ⟨-, x, hx, d, hd, hdx⟩ := hF
  exact ⟨Finset.mem_univ _, x, hx, d, hsub d hd, eqvGen_faceClass_of_agree (hagree d hd) hdx⟩

section Lobe

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- **The arc of a lobe.**  A window `L` of `invDarts B`, with `B` a window of a rotation of the
carrier of `Π`, is `invDarts T` for an arc `T` of `Π`. -/
theorem exists_arc_of_lobe {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    {l₁ L l₂ : List Delta.toCombMap.Dart} (hsplit : invDarts Delta B = l₁ ++ L ++ l₂) :
    ∃ T : CyclicArc (cellDarts Delta j), L = [] ++ invDarts Delta T.darts := by
  have hB : B = invDarts Delta l₂ ++ invDarts Delta L ++ invDarts Delta l₁ := by
    rw [← invDarts_invDarts B, hsplit, invDarts_append, invDarts_append]
    simp only [List.append_assoc]
  have hl : targetArc.darts ++ (invDarts Delta l₂ ++ invDarts Delta L ++ invDarts Delta l₁) ++
        sourceArc.darts ++ A =
      (targetArc.darts ++ invDarts Delta l₂) ++
        (invDarts Delta L ++ invDarts Delta l₁ ++ sourceArc.darts ++ A) := by
    simp only [List.append_assoc]
  have hrot : (cellDarts Delta j).rotate (n + (targetArc.darts ++ invDarts Delta l₂).length) =
      invDarts Delta L ++
        (invDarts Delta l₁ ++ sourceArc.darts ++ A ++ (targetArc.darts ++ invDarts Delta l₂)) := by
    rw [← List.rotate_rotate, hPi, hB, hl, List.rotate_append_length_eq]
    simp only [List.append_assoc]
  obtain ⟨T, hT⟩ := CyclicArc.exists_darts_eq_of_rotate_eq hrot
  exact ⟨T, by rw [hT, invDarts_invDarts, List.nil_append]⟩

/-- **A lobe reading an element other than `1` is simple.** -/
theorem isSimpleClosedWalk_lobe {L : List Delta.toCombMap.Dart}
    (hL : IsClosedDartWalk Delta.toCombMap L) (hnodup : (L.map Delta.toCombMap.vertexOf).Nodup)
    (hval : RelLetter.listVal (dartWord Delta L) ≠ 1) : IsSimpleClosedWalk Delta.toCombMap L := by
  by_cases h3 : 3 ≤ L.length
  · exact ClosedWalkInnermostLobe.isSimpleClosedWalk_of_nodup hL hnodup h3
  obtain ⟨hne, hchain, hclose⟩ := hL
  refine ⟨hne, hchain, hclose, hnodup, ?_⟩
  intro d hd hαd
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hd
  · simp only [List.mem_singleton] at hd hαd
    subst hd
    exact Delta.toCombMap.alpha_fixedPointFree _ hαd
  · have hb : b = Delta.toCombMap.alpha a := by
      simp at hd hαd
      rcases hd with rfl | rfl
      · rcases hαd with h | h
        · exact absurd h (Delta.toCombMap.alpha_fixedPointFree _)
        · exact h.symm
      · rcases hαd with h | h
        · rw [← h]
          exact (Delta.toCombMap.alpha_involutive d).symm
        · exact absurd h (Delta.toCombMap.alpha_fixedPointFree _)
    subst hb
    apply hval
    have happ : ∀ l₁ l₂ : List Delta.toCombMap.Dart,
        RelLetter.listVal (dartWord Delta (l₁ ++ l₂)) =
          RelLetter.listVal (dartWord Delta l₁) * RelLetter.listVal (dartWord Delta l₂) := by
      intro l₁ l₂
      simp [Embedded.dartWord, RelLetter.listVal]
    have hsplit : [a, Delta.toCombMap.alpha a] = [a] ++ invDarts Delta [a] := by
      simp [invDarts]
    rw [hsplit, happ, listVal_dartWord_invDarts, mul_inv_cancel]
  · simp at h3

/-- **`Π` is off the side of a lobe.**  Every dart of the lobe reverses a dart of `B`, so `Π` is
across it, and a simple walk has the face across each of its darts off its side. -/
theorem cell_not_mem_sideFaces_lobe {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    {l₁ L l₂ : List Delta.toCombMap.Dart} (hsplit : invDarts Delta B = l₁ ++ L ++ l₂)
    (hw : IsSimpleClosedWalk Delta.toCombMap L) :
    (cell Delta j).face ∉ sideFaces Delta.toCombMap L := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil L hw.ne_nil
  have hdB : Delta.toCombMap.alpha d ∈ B :=
    SameCellPocketSides.alpha_mem_of_mem_invDarts (by
      rw [hsplit]
      exact List.mem_append_left _ (List.mem_append_right _ hd))
  have hface : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = (cell Delta j).face :=
    SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hdB)))
  rw [← hface]
  exact And.right ((hw.isBoundaryDart_sideFaces_iff Delta.planar d).mpr hd)

/-- **The exterior face is off the side of a lobe**, when it is off the side of the pocket walk. -/
theorem outerFace_not_mem_sideFaces_lobe {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length)
    {l₁ L l₂ : List Delta.toCombMap.Dart} (hsplit : invDarts Delta B = l₁ ++ L ++ l₂)
    (hw : IsSimpleClosedWalk Delta.toCombMap L)
    (hout : Delta.outerFace ∉
      sideFaces Delta.toCombMap (invDarts Delta X ++ invDarts Delta B)) :
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
      z ∈ invDarts Delta X ++ invDarts Delta B → False := by
    intro z hz hzw
    have hzα : Relation.EqvGen (CombMap.FaceClassStep Delta.toCombMap
        (walkKeep Delta.toCombMap L)) d (Delta.toCombMap.alpha z) := by
      rcases hz with rfl | rfl
      · exact hdα
      · rw [Delta.toCombMap.alpha_involutive y]
        exact hdy
    rcases SameCellPocketSides.alpha_mem_of_mem_invDarts_append hzw with hX | hB
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

end Lobe

end SameCellCellLobe

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.eqvGen_faceClass_of_agree
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.sideFaces_subset_of_agree
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.exists_arc_of_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.isSimpleClosedWalk_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.cell_not_mem_sideFaces_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.outerFace_not_mem_sideFaces_lobe
