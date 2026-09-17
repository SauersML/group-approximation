import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSpurEnclosureProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: two pockets of one relator cell, enclosed from their first turns

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

Let `c = B X`.  It is nonempty and repeats no dart: `B` and `X` each repeat none, and a common dart
would lie on both `Π` and `f`.  The walk is chained by vertices and turns like a noncrossing walk
(`FirstTurnEnclosure.turnMem_of_firstTurn`).  So `enclosedFaces c`, the faces reached from the
non-walk reversals of `c` by face steps off the edges of `c`, satisfy the membership law of an
enclosed face set (`FirstTurnEnclosure.mem_iff_enclosedFaces`).  The successor law is the uniqueness
of first turns (`FirstTurnEnclosure.eq_of_firstTurn`).  This gives `EnclosedFaceSetSucc` as soon as the
exterior face is off `enclosedFaces c`.

1. *`d` is off the edges of `c`* (`not_walkKeep_of_cross`).  `d ∈ B` and `d ∈ p` contradict nodup of
   the carrier.  `d ∈ X` puts `d` on `f`, but it lies on `Π`.  `α d ∈ B` puts `α d` on `Π`, but
   `α d ∈ U` lies on `f`.  `α d ∈ X` and `α d ∈ U` contradict nodup of the face walk.
2. *`f` and `Π` are off `enclosedFaces c`* (`face_not_mem_enclosedFaces_X`).  The face step across
   `d` is allowed, so `f` is enclosed iff `Π` is (`enclosed_iff`).  One of them holds a dart of `c`:
   `X.head` on `f` or `B.head` on `Π`.  Faces of walk darts are not enclosed.
3. *The two enclosures are disjoint* (`disjoint_X_Y`).  A face step chain for `c₁ = B X`, started
   inside `enclosedFaces c₁`, stays inside it.  Its darts are not darts of `c₂ = A Y`, whose darts
   lie on `f` or `Π` (step 2).  So it is a face step chain for `c₂` too (`eqvGen_transport`).  A common
   enclosed face `g` gives `a₁ ∈ c₁` and `a₂ ∈ c₂` with `α a₁ ~₁ g ~₂ α a₂`.  From `α a₁` a `c₂`-chain
   reaches a dart of `c₂`: `α a₁` is off the edges of `c₂` (the walks share no dart,
   `not_mem_Y_of_mem_X`), and `a₁` lies on `f` or `Π`.  The face `f` or `Π` holds a dart of `c₂`
   directly, or across `e` (`exists_reach_Y`).  So a dart of `c₂` is `c₂`-related to `α a₂ ∉ c₂`,
   against `FirstTurnEnclosure.alpha_mem_of_faceClass`.
4. *Conclusion* (`pocketEnclosure`).  If the exterior face is off `enclosedFaces (B X)`, that walk
   encloses its faces without `Π`.  Otherwise, by step 3, the exterior face is off
   `enclosedFaces (A Y)`, and the rotated setting `Y U X T`, `p A q B` gives the second pocket.

This is `SameCellSpurEnclosureProof`, with the crossing darts and the first turns as hypotheses.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

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
