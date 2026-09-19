import GroupApproximation.GroupTheory.PresentedGroupRelatorReplay
import GroupApproximation.Sofic.LiteralBaseRotationRetract

/-!
# Small-step replay for the literal rotation presentation

This module is the common checker for the P13-to-rotation certificates.  Each
step names a current word, a next word, and one conjugated signed defining
relator.  The default proof is computation of an equality in a free group.
-/

namespace GroupApproximation
namespace LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

def rotationLetter? : Char → Option (RotationGenerator × Bool)
  | 'x' => some (0, true)
  | 'X' => some (0, false)
  | 'y' => some (1, true)
  | 'Y' => some (1, false)
  | 'z' => some (2, true)
  | 'Z' => some (2, false)
  | _ => none

def rotationSignedWord? : List Char → Option (SignedWord RotationGenerator)
  | [] => some []
  | c :: cs => return (← rotationLetter? c) :: (← rotationSignedWord? cs)

def rotationSignedWord (s : String)
    (h : (rotationSignedWord? s.toList).isSome := by decide) :
    SignedWord RotationGenerator :=
  (rotationSignedWord? s.toList).get h

def rotationAtom (conjugator : String) (relatorIndex : Fin 8)
    (inverted : Bool)
    (h : (rotationSignedWord? conjugator.toList).isSome := by decide) :
    Atom RotationGenerator (Fin 8) :=
  ⟨rotationSignedWord conjugator h, relatorIndex, inverted⟩

/-- One checked insertion or deletion of a conjugated signed defining
rotation relator. -/
theorem rotationStep (current next conjugator : String)
    (relatorIndex : Fin 8) (inverted : Bool)
    (hc : (rotationSignedWord? current.toList).isSome := by decide)
    (hn : (rotationSignedWord? next.toList).isSome := by decide)
    (ha : (rotationSignedWord? conjugator.toList).isSome := by decide)
    (hreplay : replayWord rotationRelator
      [rotationAtom conjugator relatorIndex inverted ha] =
      word (rotationSignedWord current hc) *
        (word (rotationSignedWord next hn))⁻¹ := by decide) :
    rotationWord (word (rotationSignedWord current hc)) =
      rotationWord (word (rotationSignedWord next hn)) :=
  mk_eq_mk_of_replay rotationRelator rotationRelator_mem _ _ _ hreplay

/-- A checked step using an already-proved consequence of the defining
rotation relators.  The free-group equality still records the exact
conjugation and orientation used by the step. -/
theorem rotationConsequenceStep (current next conjugator relation : String)
    (inverted : Bool)
    (hc : (rotationSignedWord? current.toList).isSome := by decide)
    (hn : (rotationSignedWord? next.toList).isSome := by decide)
    (ha : (rotationSignedWord? conjugator.toList).isSome := by decide)
    (hr : (rotationSignedWord? relation.toList).isSome := by decide)
    (hrelation : rotationWord (word (rotationSignedWord relation hr)) = 1)
    (hreplay : word (rotationSignedWord current hc) *
        (word (rotationSignedWord next hn))⁻¹ =
      word (rotationSignedWord conjugator ha) *
        (if inverted then (word (rotationSignedWord relation hr))⁻¹
          else word (rotationSignedWord relation hr)) *
        (word (rotationSignedWord conjugator ha))⁻¹ := by decide) :
    rotationWord (word (rotationSignedWord current hc)) =
      rotationWord (word (rotationSignedWord next hn)) := by
  apply eq_of_mul_inv_eq_one
  rw [← map_inv, ← map_mul, hreplay]
  split <;> simp [hrelation]

end

end LiteralBaseP13RotationReplay
end GroupApproximation
