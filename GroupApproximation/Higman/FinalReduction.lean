import GroupApproximation.Higman.TheoremFour
import GroupApproximation.Higman.AbsorberProgram

/-!
# Chiodo/Belegradek from four inputs

Two routes to Chiodo's Theorem 3.10 exist in this lane and had not been joined.

`Higman.TheoremFour.nonempty_universalTorsionFreeHost_of_five` runs through
`Monsters.ChiodoAbsorber` and therefore still carries
`AbsorberRecursivePresentation`, Chiodo's Proposition 3.8, as a fifth input.
`Higman.AbsorberProgram.statement_of_higman` runs through `Higman.PCAbsorber`
instead --- the same construction over the *`Primcodable`* presentation codes
--- for which Proposition 3.8 **is proved**, by
`Higman.recursivePresentationPCDirectSum` and
`Higman.recursivePresentationPCAbsorberFull`.

Composing the two gives the sharpest statement available: the whole theorem
from four inputs, every one of them a named part of Higman's own paper.

## The four

1. `OperationClosures` --- the base case `S` and closure of benignness under
   Higman's six remaining operations `ρ, τ, θ, ζ, π, ωₘ`.  Three further
   closures (intersection, union, `σ`) are proved, in
   `Higman.Operations`, `Higman.SequenceSpace` and `Higman.ShiftOperation`, and
   the base case `Z` is proved in `Higman.BaseCases`.
2. `HigmanTheoremThree` --- Higman's Section 2: every recursively enumerable
   subset of the sequence space is generated from `Z` and `S` by the nine
   operations.
3. `TransportSectionFive` --- Higman's Section 5: from the coded subgroups
   `A_B` to arbitrary recursively enumerable normal subgroups of free groups of
   finite rank.
4. `BridgeRecursive` --- that the Higman--Neumann--Neumann extension is
   recursively presented.  This is the *only* remaining clause of the bridge:
   its construction is `Higman.HNNEmbedding` and its torsion-freeness is
   `Higman.BridgeTorsion`, both proved.

Everything else --- the pinch lemma, the rope trick, the benign calculus, the
torsion-free radical and its tower, the absorber and its absorbing property,
Chiodo's Proposition 3.8 at the absorber, and the assembly of all of it --- is
proved in this repository.
-/

namespace GroupApproximation
namespace Higman

/-- **Chiodo Theorem 3.10 = Belegradek Theorem A.1, from four inputs.** -/
theorem statement_of_four (h₁ : OperationClosures) (h₂ : HigmanTheoremThree)
    (h₃ : TransportSectionFive) (h₄ : BridgeRecursive) :
    ChiodoBelegradek.Statement :=
  statement_of_higman
    (torsionFreeHigmanEmbedding_of_inputs (countableToFG_of_input h₄)
      (torsionPreservation_of_reBenignTF (reBenignTF_of_inputs h₁ h₂ h₃)))

/-- The same, landing on `KC.21`'s first input. -/
theorem nonempty_host_of_four (h₁ : OperationClosures) (h₂ : HigmanTheoremThree)
    (h₃ : TransportSectionFive) (h₄ : BridgeRecursive) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost :=
  nonempty_host_of_higman
    (torsionFreeHigmanEmbedding_of_inputs (countableToFG_of_input h₄)
      (torsionPreservation_of_reBenignTF (reBenignTF_of_inputs h₁ h₂ h₃)))

end Higman
end GroupApproximation
