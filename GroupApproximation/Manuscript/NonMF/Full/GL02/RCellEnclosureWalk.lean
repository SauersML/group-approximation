import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSpurEnclosureProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: two pockets of one relator cell, enclosed from their first turns

*GL02 copy.*  Re-proof of the foreign module `Piece04.RCellEnclosureWalk`
(origin/main blob `1eb75de54`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This module is the abstract
enclosure step behind `ClassPocketEnclosureStatement` (module `Piece04.RCellSpan`).  Its
hypotheses mention no windows, gaps or classes.

## Setting

`f` is a face and `Π = cell j` a relator cell with `Π ≠ f`.  The face walk of `f` rotates to
`X T Y U` (`htrav`), and the carrier of `Π` rotates to `q B p A` (`hPi`).  Two further facts are
assumed.

* *Crossing darts.*  Some `d ∈ p` has `α d ∈ U`, and some `e ∈ q` has `α e ∈ T`.
* *First turns.*  The complement spellings `B X` and `A Y` are chained by first turns and close up
  by a first turn (`FirstTurnClosed`).

Nothing else about `p, q, T, U` is used.  In the side-level setting `T = q⁻¹` and `U = p⁻¹`.  In the
class setting `T, U` are the side darts of the windows and `p⁻¹, q⁻¹` the whole windows, gaps
included.

## The proof

Let `c = B X`.  It is nonempty, repeats no dart, and is chained like a noncrossing walk, so
`enclosedFaces c` is an enclosed face set as soon as the exterior face is off it
(`FirstTurnEnclosure.mem_iff_enclosedFaces`, `FirstTurnEnclosure.eq_of_firstTurn`).  The crossing
dart `d` is off the edges of `c` (`not_walkKeep_of_cross`), so `f` and `Π` are off
`enclosedFaces c` (`face_not_mem_enclosedFaces_X`).  A face step chain for `B X` transports to one
for `A Y` (`eqvGen_transport`), so the two enclosures are disjoint (`disjoint_X_Y`), against
`FirstTurnEnclosure.alpha_mem_of_faceClass`.  One of the two walks misses the exterior face, which
gives `pocketEnclosure`.  This is `SameCellSpurEnclosureProof`, with the crossing darts and the
first turns as hypotheses.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.FirstTurnEnclosure

/-- A walk chained by first turns that closes up by a first turn (vacuous for the empty walk). -/
def FirstTurnClosed (M : CombMap.{v}) (c : List M.Dart) : Prop :=
  ∀ hc : c ≠ [], c.IsChain (FirstTurn M c) ∧ FirstTurn M c (c.getLast hc) (c.head hc)

namespace RCellPocketWalk

/-- Swapping the two parts of a nonempty append keeps it nonempty. -/
theorem ne_nil_swap {α : Type*} {L₁ L₂ : List α} (hne : L₁ ++ L₂ ≠ []) : L₂ ++ L₁ ≠ [] :=
  fun h => hne (by
    obtain ⟨h₁, h₂⟩ := List.append_eq_nil_iff.mp h
    rw [h₁, h₂]
    rfl)

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
  {X T Y U q B p A : List Delta.toCombMap.Dart} {r n : ℕ}

/-- The face walk repeats no dart. -/
theorem nodup_walk (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U) :
    (X ++ T ++ Y ++ U).Nodup := by
  rw [← htrav]
  exact List.nodup_rotate.mpr (Delta.faceBoundary f).nodup

/-- The carrier repeats no dart. -/
theorem nodup_carrier (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) :
    (q ++ B ++ p ++ A).Nodup := by
  rw [← hPi]
  exact List.nodup_rotate.mpr (Delta.faceBoundary (cell Delta j).face).nodup

/-- The face walk rotated to `Y U X T`, and the carrier rotated to `p A q B`. -/
theorem rotate_Y (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) :
    (Delta.faceBoundary f).darts.rotate (r + (X ++ T).length) = Y ++ U ++ X ++ T ∧
      (cellDarts Delta j).rotate (n + (q ++ B).length) = p ++ A ++ q ++ B := by
  constructor
  · rw [← List.rotate_rotate, htrav, show X ++ T ++ Y ++ U = (X ++ T) ++ (Y ++ U) by
      simp only [List.append_assoc], List.rotate_append_length_eq]
    simp only [List.append_assoc]
  · rw [← List.rotate_rotate, hPi, show q ++ B ++ p ++ A = (q ++ B) ++ (p ++ A) by
      simp only [List.append_assoc], List.rotate_append_length_eq]
    simp only [List.append_assoc]

/-- The complement spelling `B ++ X` repeats no dart. -/
theorem nodup_X (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) : (B ++ X).Nodup := by
  have hXnd : X.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp
      (nodup_walk htrav)).1).1).1
  have hBnd : B.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp
      (nodup_carrier hPi)).1).1).2.1
  exact List.nodup_append.mpr ⟨hBnd, hXnd, fun a ha b hb hab => by
    subst hab
    exact hf ((SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))).symm.trans
      (SameCellPocketSides.faceOf_of_mem_rotate htrav
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hb)))))⟩

/-- The darts of `B ++ X` lie on `f` or on `Π`. -/
theorem faceOf_of_mem_X (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A)
    {d : Delta.toCombMap.Dart} (hd : d ∈ B ++ X) :
    Delta.toCombMap.faceOf d = f ∨ Delta.toCombMap.faceOf d = (cell Delta j).face := by
  rcases List.mem_append.mp hd with hB | hX
  · exact Or.inr (SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hB))))
  · exact Or.inl (SameCellPocketSides.faceOf_of_mem_rotate htrav
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hX))))

/-- **A crossing dart of `p` is off the edges of `B ++ X`.** -/
theorem not_walkKeep_of_cross (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) {d : Delta.toCombMap.Dart}
    (hd : d ∈ p) (hdU : Delta.toCombMap.alpha d ∈ U) :
    ¬ walkKeep Delta.toCombMap (B ++ X) d := by
  have hpface : Delta.toCombMap.faceOf d = (cell Delta j).face :=
    SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_right _ hd))
  have hαface : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = f :=
    SameCellPocketSides.faceOf_of_mem_rotate htrav (List.mem_append_right _ hdU)
  rintro (h | h)
  · rcases List.mem_append.mp h with hB | hX
    · exact (SameCellPocketSides.nodup_append_four (nodup_carrier hPi)).1 _
        (List.mem_append_right _ hB) _ hd rfl
    · exact hf (hpface.symm.trans (SameCellPocketSides.faceOf_of_mem_rotate htrav
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hX)))))
  · rcases List.mem_append.mp h with hB | hX
    · exact hf ((SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hB)))).symm.trans
        hαface)
    · exact (SameCellPocketSides.nodup_append_four (nodup_walk htrav)).2 _
        (List.mem_append_left _ (List.mem_append_left _ hX)) _ hdU rfl

/-- `f` is enclosed by `B ++ X` iff `Π` is: the face step across the crossing dart is allowed. -/
theorem enclosed_iff (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) {d : Delta.toCombMap.Dart}
    (hd : d ∈ p) (hdU : Delta.toCombMap.alpha d ∈ U) :
    f ∈ enclosedFaces Delta.toCombMap (B ++ X) ↔
      (cell Delta j).face ∈ enclosedFaces Delta.toCombMap (B ++ X) := by
  have hpface : Delta.toCombMap.faceOf d = (cell Delta j).face :=
    SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_right _ hd))
  have hαface : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = f :=
    SameCellPocketSides.faceOf_of_mem_rotate htrav (List.mem_append_right _ hdU)
  have hkeep := not_walkKeep_of_cross hf htrav hPi hd hdU
  constructor
  · intro h
    have h' := faceOf_alpha_mem_enclosedFaces (c := B ++ X)
      (x := Delta.toCombMap.alpha d) (by rwa [walkKeep_alpha]) (by rw [hαface]; exact h)
    rwa [Delta.toCombMap.alpha_involutive, hpface] at h'
  · intro h
    have h' := faceOf_alpha_mem_enclosedFaces hkeep (by rw [hpface]; exact h)
    rwa [hαface] at h'

/-- **`f` and `Π` are off the faces enclosed by `B ++ X`.** -/
theorem face_not_mem_enclosedFaces_X (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) {d : Delta.toCombMap.Dart}
    (hd : d ∈ p) (hdU : Delta.toCombMap.alpha d ∈ U) (hne : X ++ B ≠ [])
    (hturn : FirstTurnClosed Delta.toCombMap (B ++ X)) :
    f ∉ enclosedFaces Delta.toCombMap (B ++ X) ∧
      (cell Delta j).face ∉ enclosedFaces Delta.toCombMap (B ++ X) := by
  have hc : B ++ X ≠ [] := ne_nil_swap hne
  obtain ⟨hfchain, hclose⟩ := hturn hc
  have hchain : (B ++ X).IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e :=
    hfchain.imp fun _ _ h => h.vertexOf_eq
  have hturnMem := turnMem_of_firstTurn hc hfchain hclose
  have hiff := enclosed_iff hf htrav hPi hd hdU
  by_cases hX : X = []
  · have hB : B ≠ [] := by
      rintro rfl
      exact hne (by rw [hX]; rfl)
    have hmem : B.head hB ∈ B ++ X := List.mem_append_left _ (List.head_mem hB)
    have hBface : Delta.toCombMap.faceOf (B.head hB) = (cell Delta j).face :=
      SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.head_mem hB))))
    have hcellOut := faceOf_not_mem_enclosedFaces Delta.planar hc hchain hturnMem hmem
    rw [hBface] at hcellOut
    exact ⟨fun h => hcellOut (hiff.mp h), hcellOut⟩
  · have hmem : X.head hX ∈ B ++ X := List.mem_append_right _ (List.head_mem hX)
    have hXface : Delta.toCombMap.faceOf (X.head hX) = f :=
      SameCellPocketSides.faceOf_of_mem_rotate htrav
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.head_mem hX))))
    have hfOut := faceOf_not_mem_enclosedFaces Delta.planar hc hchain hturnMem hmem
    rw [hXface] at hfOut
    exact ⟨hfOut, fun h => hfOut (hiff.mpr h)⟩

/-- **The complement spelling `B ++ X` encloses its faces**, in the successor form, when the exterior
face is off them. -/
theorem enclosedFaceSetSucc_X (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) (hne : X ++ B ≠ [])
    (hturn : FirstTurnClosed Delta.toCombMap (B ++ X))
    (hout : Delta.outerFace ∉ enclosedFaces Delta.toCombMap (B ++ X)) :
    EnclosedFaceSetSucc Delta (enclosedFaces Delta.toCombMap (B ++ X)) (B ++ X) := by
  have hc : B ++ X ≠ [] := ne_nil_swap hne
  obtain ⟨hfchain, hclose⟩ := hturn hc
  have hchain : (B ++ X).IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e :=
    hfchain.imp fun _ _ h => h.vertexOf_eq
  have hturnMem := turnMem_of_firstTurn hc hfchain hclose
  exact
    { outerFace_not_mem := hout
      ne_nil := hc
      nodup := nodup_X hf htrav hPi
      chain := hchain
      closes := hclose.vertexOf_eq
      mem_iff := mem_iff_enclosedFaces Delta.planar hc hchain hturnMem
      turn_mem := hturnMem
      turn_next := fun _ hi _ hm hkeep hfirst =>
        eq_of_firstTurn (firstTurn_getElem_succ hc hfchain hclose hi (Nat.mod_lt _ (by omega)))
          (List.getElem_mem _) hm hkeep hfirst }

/-- The walks `B ++ X` and `A ++ Y` share no dart. -/
theorem not_mem_Y_of_mem_X (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A)
    {d : Delta.toCombMap.Dart} (hd₁ : d ∈ B ++ X) (hd₂ : d ∈ A ++ Y) : False := by
  rcases List.mem_append.mp hd₁ with hB | hX <;> rcases List.mem_append.mp hd₂ with hA | hY
  · exact (SameCellPocketSides.nodup_append_four (nodup_carrier hPi)).2 _
      (List.mem_append_left _ (List.mem_append_right _ hB)) _ hA rfl
  · exact hf ((SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hB)))).symm.trans
      (SameCellPocketSides.faceOf_of_mem_rotate htrav
        (List.mem_append_left _ (List.mem_append_right _ hY))))
  · exact hf ((SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_right _ hA)).symm.trans (SameCellPocketSides.faceOf_of_mem_rotate htrav
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hX)))))
  · exact (SameCellPocketSides.nodup_append_four (nodup_walk htrav)).1 _
      (List.mem_append_left _ hX) _ hY rfl

/-- **From a dart on `f` or on `Π`, a chain off the edges of `A ++ Y` reaches a dart of it**: around
the face, and across the crossing dart `e ∈ q` when the other face holds the walk. -/
theorem exists_reach_Y (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) {e : Delta.toCombMap.Dart}
    (he : e ∈ q) (heT : Delta.toCombMap.alpha e ∈ T) (hne : Y ++ A ≠ [])
    {z : Delta.toCombMap.Dart}
    (hz : Delta.toCombMap.faceOf z = f ∨ Delta.toCombMap.faceOf z = (cell Delta j).face) :
    ∃ d ∈ A ++ Y, Relation.EqvGen
      (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap (A ++ Y))) z d := by
  obtain ⟨htrav', hPi'⟩ := rotate_Y htrav hPi
  have hkeep := not_walkKeep_of_cross hf htrav' hPi' he heT
  have hqface : Delta.toCombMap.faceOf e = (cell Delta j).face :=
    SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))
  have hαface : Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) = f :=
    SameCellPocketSides.faceOf_of_mem_rotate htrav
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ heT)))
  have hface : ∀ x y : Delta.toCombMap.Dart, Delta.toCombMap.faceOf x = Delta.toCombMap.faceOf y →
      Relation.EqvGen
        (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap (A ++ Y))) x y :=
    fun x y h =>
      eqvGen_faceClass_of_sameCycle Delta.toCombMap _ ((Delta.toCombMap.faceOf_eq_iff x y).mp h)
  have hcross : Relation.EqvGen
      (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap (A ++ Y)))
      e (Delta.toCombMap.alpha e) :=
    .rel _ _ (Or.inr ⟨hkeep, rfl⟩)
  by_cases hY : Y = []
  · have hA : A ≠ [] := by
      rintro rfl
      exact hne (by rw [hY]; rfl)
    have hAface : Delta.toCombMap.faceOf (A.head hA) = (cell Delta j).face :=
      SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
        (List.mem_append_right _ (List.head_mem hA))
    refine ⟨A.head hA, List.mem_append_left _ (List.head_mem hA), ?_⟩
    rcases hz with hz | hz
    · exact .trans _ _ _ (hface _ _ (hz.trans hαface.symm))
        (.trans _ _ _ (.symm _ _ hcross) (hface _ _ (hqface.trans hAface.symm)))
    · exact hface _ _ (hz.trans hAface.symm)
  · have hYface : Delta.toCombMap.faceOf (Y.head hY) = f :=
      SameCellPocketSides.faceOf_of_mem_rotate htrav
        (List.mem_append_left _ (List.mem_append_right _ (List.head_mem hY)))
    refine ⟨Y.head hY, List.mem_append_right _ (List.head_mem hY), ?_⟩
    rcases hz with hz | hz
    · exact hface _ _ (hz.trans hYface.symm)
    · exact .trans _ _ _ (hface _ _ (hz.trans hqface.symm))
        (.trans _ _ _ hcross (hface _ _ (hαface.trans hYface.symm)))

/-- **Transport of face step chains.**  A chain for `c₁` started inside `enclosedFaces c₁` is a chain
for `c₂`, when no dart on an enclosed face of `c₁` is a dart of `c₂`. -/
theorem eqvGen_transport {M : CombMap.{v}} {c₁ c₂ : List M.Dart}
    (hoff : ∀ y : M.Dart, M.faceOf y ∈ enclosedFaces M c₁ → y ∉ c₂) :
    ∀ y z : M.Dart, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c₁)) y z →
      M.faceOf y ∈ enclosedFaces M c₁ →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c₂)) y z := by
  have hclos : ∀ y z : M.Dart, M.faceOf y ∈ enclosedFaces M c₁ →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c₁)) y z →
      M.faceOf z ∈ enclosedFaces M c₁ := fun y z hy h => by
    obtain ⟨a, ha, hna, h'⟩ := (mem_enclosedFaces_iff _ _ y).mp hy
    exact (mem_enclosedFaces_iff _ _ z).mpr ⟨a, ha, hna, .trans _ _ _ h' h⟩
  intro y z h
  induction h with
  | rel y z hyz =>
    intro hy
    rcases hyz with hyz | ⟨hk, hyz⟩
    · exact .rel _ _ (Or.inl hyz)
    · refine .rel _ _ (Or.inr ⟨?_, hyz⟩)
      rintro (hy₂ | hαy₂)
      · exact hoff y hy hy₂
      · exact hoff _ (faceOf_alpha_mem_enclosedFaces hk hy) hαy₂
  | refl y => intro _; exact .refl _
  | symm y z h ih => intro hz; exact .symm _ _ (ih (hclos z y hz (.symm _ _ h)))
  | trans y z w hyz _ ih₁ ih₂ => intro hy; exact .trans _ _ _ (ih₁ hy) (ih₂ (hclos y z hy hyz))

/-- **The two complement spellings enclose disjoint faces.** -/
theorem disjoint_X_Y (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) {d e : Delta.toCombMap.Dart}
    (hd : d ∈ p) (hdU : Delta.toCombMap.alpha d ∈ U) (he : e ∈ q)
    (heT : Delta.toCombMap.alpha e ∈ T) (hne₁ : X ++ B ≠ [])
    (hturn₁ : FirstTurnClosed Delta.toCombMap (B ++ X)) (hne₂ : Y ++ A ≠ [])
    (hturn₂ : FirstTurnClosed Delta.toCombMap (A ++ Y)) {g : Delta.toCombMap.Face}
    (hg₁ : g ∈ enclosedFaces Delta.toCombMap (B ++ X))
    (hg₂ : g ∈ enclosedFaces Delta.toCombMap (A ++ Y)) : False := by
  obtain ⟨htrav', hPi'⟩ := rotate_Y htrav hPi
  have hF₁ := face_not_mem_enclosedFaces_X hf htrav hPi hd hdU hne₁ hturn₁
  have hc₂ : A ++ Y ≠ [] := ne_nil_swap hne₂
  obtain ⟨hfchain₂, hclose₂⟩ := hturn₂ hc₂
  have hchain₂ : (A ++ Y).IsChain fun a b =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha a) = Delta.toCombMap.vertexOf b :=
    hfchain₂.imp fun _ _ h => h.vertexOf_eq
  have hturnMem₂ := turnMem_of_firstTurn hc₂ hfchain₂ hclose₂
  have hoff : ∀ y : Delta.toCombMap.Dart,
      Delta.toCombMap.faceOf y ∈ enclosedFaces Delta.toCombMap (B ++ X) → y ∉ A ++ Y := by
    intro y hy hy₂
    rcases faceOf_of_mem_X htrav' hPi' hy₂ with h | h
    · exact hF₁.1 (by rw [← h]; exact hy)
    · exact hF₁.2 (by rw [← h]; exact hy)
  have htransport := eqvGen_transport hoff
  obtain ⟨x, rfl⟩ := Quotient.exists_rep g
  obtain ⟨a₁, ha₁, hna₁, hx₁⟩ := (mem_enclosedFaces_iff _ _ x).mp hg₁
  obtain ⟨a₂, ha₂, hna₂, hx₂⟩ := (mem_enclosedFaces_iff _ _ x).mp hg₂
  have hseed : Delta.toCombMap.faceOf (Delta.toCombMap.alpha a₁) ∈
      enclosedFaces Delta.toCombMap (B ++ X) :=
    (mem_enclosedFaces_iff _ _ _).mpr ⟨a₁, ha₁, hna₁, .refl _⟩
  have h₂₁ := Relation.EqvGen.trans _ _ _ hx₂ (.symm _ _ (htransport _ _ hx₁ hseed))
  obtain ⟨b, hb, hreach⟩ : ∃ b ∈ A ++ Y, Relation.EqvGen
      (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap (A ++ Y)))
      (Delta.toCombMap.alpha a₁) b := by
    by_cases hα : Delta.toCombMap.alpha a₁ ∈ A ++ Y
    · exact ⟨_, hα, .refl _⟩
    · have hk : ¬ walkKeep Delta.toCombMap (A ++ Y) (Delta.toCombMap.alpha a₁) := by
        rintro (h | h)
        · exact hα h
        · rw [Delta.toCombMap.alpha_involutive] at h
          exact not_mem_Y_of_mem_X hf htrav hPi ha₁ h
      obtain ⟨b, hb, hz⟩ := exists_reach_Y hf htrav hPi he heT hne₂
        (faceOf_of_mem_X htrav hPi ha₁)
      refine ⟨b, hb, .trans _ _ _ (.rel _ _ (Or.inr ⟨hk, ?_⟩)) hz⟩
      rw [Delta.toCombMap.alpha_involutive]
  exact hna₂ (alpha_mem_of_faceClass Delta.planar hc₂ hchain₂ hturnMem₂ hb ha₂
    (.symm _ _ (.trans _ _ _ h₂₁ hreach)))

/-- **The pocket enclosure.**  The exterior face is off one of the two disjoint enclosures, and that
complement spelling encloses its faces with `Π` outside. -/
theorem pocketEnclosure (hf : (cell Delta j).face ≠ f)
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ T ++ Y ++ U)
    (hPi : (cellDarts Delta j).rotate n = q ++ B ++ p ++ A) {d e : Delta.toCombMap.Dart}
    (hd : d ∈ p) (hdU : Delta.toCombMap.alpha d ∈ U) (he : e ∈ q)
    (heT : Delta.toCombMap.alpha e ∈ T) (hne₁ : X ++ B ≠ []) (hne₂ : Y ++ A ≠ [])
    (hturn₁ : FirstTurnClosed Delta.toCombMap (B ++ X))
    (hturn₂ : FirstTurnClosed Delta.toCombMap (A ++ Y)) :
    (∃ F : Finset Delta.toCombMap.Face,
        EnclosedFaceSetSucc Delta F (B ++ X) ∧ (cell Delta j).face ∉ F) ∨
      ∃ F : Finset Delta.toCombMap.Face,
        EnclosedFaceSetSucc Delta F (A ++ Y) ∧ (cell Delta j).face ∉ F := by
  obtain ⟨htrav', hPi'⟩ := rotate_Y htrav hPi
  by_cases hout : Delta.outerFace ∈ enclosedFaces Delta.toCombMap (B ++ X)
  · exact Or.inr ⟨_, enclosedFaceSetSucc_X hf htrav' hPi' hne₂ hturn₂
      fun h => disjoint_X_Y hf htrav hPi hd hdU he heT hne₁ hturn₁ hne₂ hturn₂ hout h,
      (face_not_mem_enclosedFaces_X hf htrav' hPi' he heT hne₂ hturn₂).2⟩
  · exact Or.inl ⟨_, enclosedFaceSetSucc_X hf htrav hPi hne₁ hturn₁ hout,
      (face_not_mem_enclosedFaces_X hf htrav hPi hd hdU hne₁ hturn₁).2⟩

end RCellPocketWalk

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RCellPocketWalk.pocketEnclosure
