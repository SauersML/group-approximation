import GroupApproximation.Higman.FinalReduction
import GroupApproximation.Higman.FlipGroup
import GroupApproximation.Higman.OperationClosureTau
import GroupApproximation.Higman.TorsionFreeImageClosure

/-!
# `OperationClosures` from what is actually still open

`Higman.Operations` states the first of the four inputs of
`Higman.FinalReduction` as one structure, `OperationClosures`, with seven
fields: the base case `S` and the six operation closures `ρ, τ, θ, ζ, π, ωₘ`.
That count was accurate when the structure was written and is not accurate now.
Since then

* `Higman.TorsionFreeImageClosure` **proved** `Seq.TorsionFreeImageClosure`,
  the image half of Higman's Lemma 3.3 with the torsion clause, off the back of
  `Algebra.PushoutITorsionFree`;
* `Higman.FlipGroup` reduced `ρ` to exactly that statement
  (`Flip.benignTF_ASub_rhoOp_of_imageClosure`);
* `Higman.OmegaClosure` reduced `ζ`, `π` and `ωₘ` to three named facts ---
  two rows and `Omega.OmegaInput` (`Omega.zeta_pi_omega_closures`);
* `Higman.OperationClosureTheta` reduced `θ` to two of those same facts, a
  third row and no `TorsionFreeImageClosure` at all
  (`Seq.benignTF_ASub_thetaOp_of_lanes`).

This file does the bookkeeping those four results imply.
`operationClosures_of_inputs` builds the whole structure from

1. `Omega.OmegaInput`;
2. the `τ` closure;
3. the base case `S`;
4. three benign-row facts --- the positive half-row, the normal closure of `b`
   in the row, and the even-coordinate row.

`ρ` does not appear: it is discharged here, by importing the module that proves
its one input.  That import is the point of this file as much as the
constructor is --- `Higman.TorsionFreeImageClosure` is otherwise reachable from
no root, so the theorem it proves was not being compiled at all.

The two corollaries at the end thread the constructor through
`Higman.FinalReduction`, so that Chiodo's Theorem 3.10 and `KC.21`'s first
input are both available from six inputs plus Higman's Sections 2 and 5 and the
bridge, rather than from the seven-field structure.

## What this does *not* claim

Nothing here proves any of the six arguments.  The base case `S`, the `τ`
closure, `OmegaInput` and the three rows are open exactly as they were; the
only change is that `ρ` has left the list and the remaining entries are stated
at the sharpest shape the repository can consume them at.  In particular
`Seq.SwapWitness`, which `operationClosures_of_swap` accepts in place of the
`τ` closure, is *stronger* than the closure and is offered only because it is
the shape `Higman.OperationClosureTau` builds towards.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  `ρ` is no longer an input -/

/-- **Higman's operation `ρ` preserves benignness with a torsion-free
witness.**  The `ρ` field of `OperationClosures`, proved: `Higman.FlipGroup`
reduces it to `Seq.TorsionFreeImageClosure` and
`Higman.TorsionFreeImageClosure` proves that. -/
theorem operationClosures_rho (B : Set Seq.E) (h : BenignTF (Seq.ASub B)) :
    BenignTF (Seq.ASub (Seq.rhoOp B)) :=
  Flip.benignTF_ASub_rhoOp_of_imageClosure Seq.torsionFreeImageClosure B h

/-! ## 2.  The structure, from the leaves that are open -/

/-- **`OperationClosures` from six inputs.**

`k` is the `ω` residue of `Higman.OmegaClosure`; `htau` is Higman's `τ`;
`hbase` is his base case `S`; and `hhalf`, `hzetaRow`, `hevenRow` are the three
benign rows --- the positive half-row (Higman's Example 3.7), the normal
closure of `b` in the row, and the row cut out by the even coordinates.

The seventh field, `ρ`, is `operationClosures_rho`, and the subgroup of all
coded sequences --- which the agreement closures also consume --- is not an
input either: `Omega.benignTF_ASub_univ` derives it from `k`. -/
theorem operationClosures_of_inputs (k : Omega.OmegaInput)
    (htau : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
      BenignTF (Seq.ASub (Seq.tauOp B)))
    (hbase : BenignTF (Seq.ASub Seq.Sset))
    (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzetaRow : BenignTF (Agree.rowSub Agree.zetaV))
    (hevenRow : BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx)))) :
    OperationClosures :=
  have hzpo := Omega.zeta_pi_omega_closures hhalf hzetaRow k
  { base := hbase
    rho := operationClosures_rho
    tau := htau
    theta := Seq.benignTF_ASub_thetaOp_of_lanes hevenRow k
    zeta := hzpo.1
    pi := hzpo.2.1
    omega := hzpo.2.2 }

/-- **The same, taking `Higman.OperationClosureTau`'s swap in place of the `τ`
closure.**  `Seq.SwapWitness` is strictly stronger than the closure it
produces, so this is the convenience form, not the sharp one. -/
theorem operationClosures_of_swap (k : Omega.OmegaInput) (w : Seq.SwapWitness)
    (hbase : BenignTF (Seq.ASub Seq.Sset))
    (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzetaRow : BenignTF (Agree.rowSub Agree.zetaV))
    (hevenRow : BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx)))) :
    OperationClosures :=
  operationClosures_of_inputs k (Seq.benignTF_ASub_tauOp_of_swap w) hbase hhalf
    hzetaRow hevenRow

/-! ## 3.  Threading it through the final reduction

`Higman.FinalReduction` states Chiodo's Theorem 3.10 from four inputs, the
first of which is `OperationClosures`.  Substituting the constructor above
replaces that input by the six leaves it is actually built from. -/

/-- **Chiodo Theorem 3.10 = Belegradek Theorem A.1, with `ρ` removed from the
input list.**  `Higman.FinalReduction.statement_of_four` at
`operationClosures_of_inputs`. -/
theorem statement_of_operationInputs (k : Omega.OmegaInput)
    (htau : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
      BenignTF (Seq.ASub (Seq.tauOp B)))
    (hbase : BenignTF (Seq.ASub Seq.Sset))
    (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzetaRow : BenignTF (Agree.rowSub Agree.zetaV))
    (hevenRow : BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx))))
    (h₂ : HigmanTheoremThree) (h₃ : TransportSectionFive) (h₄ : BridgeRecursive) :
    ChiodoBelegradek.Statement :=
  statement_of_four
    (operationClosures_of_inputs k htau hbase hhalf hzetaRow hevenRow) h₂ h₃ h₄

/-- The same, landing on `KC.21`'s first input. -/
theorem nonempty_host_of_operationInputs (k : Omega.OmegaInput)
    (htau : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
      BenignTF (Seq.ASub (Seq.tauOp B)))
    (hbase : BenignTF (Seq.ASub Seq.Sset))
    (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzetaRow : BenignTF (Agree.rowSub Agree.zetaV))
    (hevenRow : BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx))))
    (h₂ : HigmanTheoremThree) (h₃ : TransportSectionFive) (h₄ : BridgeRecursive) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost :=
  nonempty_host_of_four
    (operationClosures_of_inputs k htau hbase hhalf hzetaRow hevenRow) h₂ h₃ h₄

end Higman
end GroupApproximation
