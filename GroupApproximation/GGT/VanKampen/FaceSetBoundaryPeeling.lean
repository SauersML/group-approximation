import GroupApproximation.GGT.VanKampen.FaceSetWordHomotopy

/-!
# Local face-peel witnesses and finite termination

`Estimating.Embedded.FaceSetBoundary` records one cyclic boundary walk, but a
walk alone does not name the face that is peeled next.  This file isolates
that missing *local* datum.  `FaceSetBoundaryPeelWitness` says that a selected
face meets the current walk in a nonempty arc and supplies a finite sequence
of face insertions/erasures and internal `alpha` cancellations taking the
walk to the next one.  The remaining nonempty region is represented by a new
`FaceSetBoundary`; when no faces remain the next word is required to be `[]`.

The theorem `faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle` is the
face-count induction.  Thus any planar extremal-face/Euler lemma only has to
produce one `FaceSetBoundaryPeelWitness` at a time.  This is deliberately
separate from est's boundary structure: its current fields do not contain
the required extremal-face assertion, and no topological fact is hidden in a
word-rewriting constructor.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqBoundaryPeeling :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-- One geometrically exposed face and the finite word factorisation which
removes it.  The `arc_factor` field is the nonempty boundary arc required by
the planar peel lemma; `moves` may include insertion of the face's remaining
boundary followed by internal `alpha`-pair cancellations. -/
structure FaceSetBoundaryPeelWitness
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) where
  face : Delta.toCombMap.Face
  face_mem : face ∈ faces
  face_ne_outer : face ≠ Delta.outerFace
  next : List Delta.toCombMap.Dart
  arc : List Delta.toCombMap.Dart
  arc_nonempty : arc ≠ []
  arc_factor : ∃ before after : List Delta.toCombMap.Dart,
    boundary.cycle = before ++ arc ++ after
  moves : FaceSetMoveSequence (faces := faces) boundary.cycle next
  remainder :
    (faces.erase face = ∅ ∧ next = []) ∨
      ∃ boundary' : FaceSetBoundary Delta (faces.erase face),
        boundary'.cycle = next

/-- A local peel oracle, parametrised over every nonempty single-cycle
`G`-region in the diagram. -/
abbrev FaceSetBoundaryPeelOracle : Prop :=
  ∀ {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces),
    FaceSetBoundaryPeelWitness boundary

/-- Face-count termination assembles local peel witnesses into a complete
`FaceSetBoundaryPeeling`.  This is the induction used by both the one-face
and adjacent-face cases; the only geometric input is the one-step oracle. -/
theorem faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (oracle : FaceSetBoundaryPeelOracle (Delta := Delta)) :
    FaceSetBoundaryPeeling boundary := by
  have aux : ∀ n : ℕ,
      ∀ {faces : Finset Delta.toCombMap.Face}
        (boundary : FaceSetBoundary Delta faces),
        faces.card = n →
          FaceSetDeletionSchedule (Delta := Delta) faces boundary.cycle := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro faces boundary hcard
        obtain ⟨face, hface, hne, next, arc, harc, hfactor, moves,
          hremainder⟩ := oracle boundary
        rcases hremainder with hempty | hnonempty
        · rcases hempty with ⟨herase, hnext⟩
          subst next
          have htail :
              FaceSetDeletionSchedule (Delta := Delta) (faces.erase face) [] := by
            rw [herase]
            exact FaceSetDeletionSchedule.empty
          exact FaceSetDeletionSchedule.step face hface hne
            moves.to_homotopy htail
        · obtain ⟨boundary', hcycle⟩ := hnonempty
          have hlt : (faces.erase face).card < n := by
            rw [← hcard]
            exact Finset.card_erase_lt_of_mem hface
          have htail := ih (faces.erase face).card hlt boundary' rfl
          rw [← hcycle] at htail
          exact FaceSetDeletionSchedule.step face hface hne
            moves.to_homotopy htail
  exact ⟨aux faces.card boundary rfl⟩

/-- The one-face model is obtained from the direct face-boundary move. -/
theorem oneFacePeelWitness
    {face : Delta.toCombMap.Face} (hne : face ≠ Delta.outerFace) :
    FaceSetDeletionSchedule (Delta := Delta) {face}
      (Delta.faceBoundary face).darts :=
  FaceSetDeletionSchedule.oneFace face hne

/-- Two adjacent selected faces are handled by two successive witnesses.  The
first witness may use an arbitrary finite insertion/cancellation sequence;
the theorem only consumes its `FaceSetMoveSequence` endpoint. -/
theorem twoFacePeeling
    {faces : Finset Delta.toCombMap.Face}
    {f₁ f₂ : Delta.toCombMap.Face}
    (hfaces : faces = {f₁, f₂})
    (hneq : f₁ ≠ f₂)
    (h₁ : f₁ ≠ Delta.outerFace) (h₂ : f₂ ≠ Delta.outerFace)
    (h₁mem : f₁ ∈ faces) (h₂mem : f₂ ∈ faces)
    (cycle next : List Delta.toCombMap.Dart)
    (moves : FaceSetMoveSequence (faces := faces) cycle next)
    (hnext : next = (Delta.faceBoundary f₂).darts) :
    FaceSetDeletionSchedule (Delta := Delta) faces cycle := by
  subst faces
  have htail : FaceSetDeletionSchedule (Delta := Delta) ({f₂} : Finset _)
      (Delta.faceBoundary f₂).darts :=
    oneFace f₂ h₂
  rw [hnext] at moves
  have hstep := FaceSetDeletionSchedule.step f₁
    (by simpa [hneq] using h₁mem) h₁ moves htail
  simpa [hneq] using hstep

end Embedded
end VanKampen
end GGT
end GroupApproximation
