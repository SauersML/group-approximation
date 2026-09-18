import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVPresentReduce
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finite.Prod
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite presentability of `V_d` from short relators among the short cone swaps (bh-met-77)

Target: `HigmanVFinFPStatement` (`EnvelopeHigmanVAlphabet.lean`), for every `d ≥ 2` the group
`higmanThompsonV (Fin d)` is finitely presented.

Route.
* Fix the finite relator set `higmanVFPRelators d`: the kernel elements of
  `FreeGroup.lift (vgenShortSwaps (Fin d))` of reduced length at most `higmanVFPBound d = 8d+64`.
  The involution, symmetry, comparable-letter, commutation and conjugation relators (reduced
  length at most `4`) and the split relators `(v w) = ∏ₐ (va wa)` (length `d+1`) all lie in it
  (`EnvelopeHigmanVFPLetters.lean`, `EnvelopeHigmanVFPSplitRel.lean`).
* `higmanVFP_relators_finite`: it is finite, since `toWord` is injective into the finite set of
  lists of length at most `8d+64` over `Fin n × Bool`.
* `higmanVFP_relators_subset_ker`: it lies in the kernel (by definition).
* `higmanVFP_swapGenShortSection_of_complete`: if its normal closure contains the kernel, the
  surjection `FreeGroup.lift (vgenShortSwaps (Fin d))` (`swapGen_shortSwaps_closure_eq_top`) has a
  unital intertwining section modulo it (`higmanVPresent_section`), which is the existing
  `SwapGenShortSectionStatement`, hence `HigmanVFinFPStatement`.

**Remaining gap (LOUD).**  `HigmanVFPShortCompleteStatement`: the kernel is contained in the
normal closure of `higmanVFPRelators d`.  It is NOT weaker than the target in logical strength:
it *implies* `HigmanVFinFPStatement` and asserts in addition an explicit bound `8d+64` on the
lengths of a set of defining relators in the depth-`≤ 3` cone swaps (the `∃`-bound version would
be equivalent to the target, so it is not used).  It is strictly smaller in proof content: the
choice of generators, generation, finiteness of the relators, the Tietze/section step and the
passage to arbitrary alphabets are all discharged here.

*Truth.*  Believed true (it is the explicit-length form of Higman's theorem; for `d = 2` the
depth-`≤ 3` cone swaps with the four Bleak–Quick relator families, all of length `≤ 4`, present
`V`), but NOT verified here, in particular not for `d > 2` with this bound.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Balls in a free group on a finite alphabet are finite.** -/
theorem higmanVFP_ball_finite {α : Type*} [Finite α] [DecidableEq α] (L : ℕ) :
    {x : FreeGroup α | FreeGroup.norm x ≤ L}.Finite :=
  (Set.Finite.preimage FreeGroup.toWord_injective.injOn
    (List.finite_length_le (α × Bool) L)).subset fun _ hx => hx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_ball_finite

/-- The length bound `8d + 64` for the defining relators among the short cone swaps of `V_d`. -/
def higmanVFPBound (d : ℕ) : ℕ :=
  8 * d + 64

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPBound

/-- The relators: kernel elements of the short-swap evaluation of reduced length at most
`higmanVFPBound d`. -/
def higmanVFPRelators (d : ℕ) : Set (FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d))))) :=
  {r | r ∈ (FreeGroup.lift (vgenShortSwaps (Fin d))).ker ∧ FreeGroup.norm r ≤ higmanVFPBound d}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPRelators

/-- The relator set is finite. -/
theorem higmanVFP_relators_finite (d : ℕ) : (higmanVFPRelators d).Finite :=
  (higmanVFP_ball_finite (higmanVFPBound d)).subset fun _ hr => hr.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_relators_finite

/-- The relators lie in the kernel of the short-swap evaluation. -/
theorem higmanVFP_relators_subset_ker (d : ℕ) :
    higmanVFPRelators d ⊆ (FreeGroup.lift (vgenShortSwaps (Fin d))).ker :=
  fun _ hr => hr.1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_relators_subset_ker

/-- The normal closure of the relators lies in the kernel. -/
theorem higmanVFP_normalClosure_le_ker (d : ℕ) :
    Subgroup.normalClosure (higmanVFPRelators d) ≤
      (FreeGroup.lift (vgenShortSwaps (Fin d))).ker :=
  Subgroup.normalClosure_le_normal (higmanVFP_relators_subset_ker d)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_normalClosure_le_ker

/-- **The remaining gap (explicit-length Higman theorem).**  For `d ≥ 2`, every relation among
the short cone swaps of `V_d` is a consequence of those of reduced length at most `8d + 64`.
Strictly smaller in proof content than `HigmanVFinFPStatement` (see the module docstring); it is
logically stronger, not equivalent, and believed true but not verified. -/
def HigmanVFPShortCompleteStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    (FreeGroup.lift (vgenShortSwaps (Fin d))).ker ≤ Subgroup.normalClosure (higmanVFPRelators d)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVFPShortCompleteStatement

/-- Under the gap, the kernel equals the normal closure of the short relators. -/
theorem higmanVFP_ker_eq_of_complete (h : HigmanVFPShortCompleteStatement) (d : ℕ)
    (hd : 1 < d) :
    (FreeGroup.lift (vgenShortSwaps (Fin d))).ker = Subgroup.normalClosure (higmanVFPRelators d) :=
  le_antisymm (h d hd) (higmanVFP_normalClosure_le_ker d)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_ker_eq_of_complete

/-- **Relators and section from the gap.** -/
theorem higmanVFP_swapGenShortSection_of_complete (h : HigmanVFPShortCompleteStatement) :
    SwapGenShortSectionStatement := by
  intro d hd
  have hsurj : Function.Surjective (FreeGroup.lift (vgenShortSwaps (Fin d))) := by
    rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]
    exact swapGen_shortSwaps_closure_eq_top d hd
  obtain ⟨s, hs1, hmul⟩ := higmanVPresent_section (FreeGroup.lift (vgenShortSwaps (Fin d))) hsurj
    (Subgroup.normalClosure (higmanVFPRelators d)) (h d hd)
  refine ⟨higmanVFPRelators d, higmanVFP_relators_finite d, higmanVFP_relators_subset_ker d, s,
    hs1, fun v i => ?_⟩
  rw [hmul v (FreeGroup.of i), FreeGroup.lift_apply_of]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_swapGenShortSection_of_complete

/-- **The lane target from the gap.**  Each `V_d` (`d ≥ 2`) is finitely presented. -/
theorem higmanVFP_finFP_of_complete (h : HigmanVFPShortCompleteStatement) :
    HigmanVFinFPStatement :=
  higmanVPresent_finFP_of_swapGenShortSection (higmanVFP_swapGenShortSection_of_complete h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_finFP_of_complete

/-- Higman's theorem over every finite nontrivial alphabet from the gap. -/
theorem higmanVFP_of_complete (h : HigmanVFPShortCompleteStatement) : HigmanVFPStatement :=
  higmanVFP_of_fin (higmanVFP_finFP_of_complete h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_of_complete

end GroupApproximation.BooneHigman.Metabelian.Envelope
