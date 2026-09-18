import GroupApproximation.BooneHigman.Metabelian.EnvelopeRN
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity of `[V_X(H), V_X(H)]`: the target statement

For a finite alphabet `X` with at least two letters and a self-similar `H ≤ Aut(T_X)`, the
commutator subgroup of the Röver–Nekrashevych group `V_X(H)` (`roverNekrashevych X H`) is
simple (Nekrashevych, *Finitely presented groups associated with expanding maps*, Thm 4.7).

`RNCommutatorSimpleStatement'` records this for every such `X` and `H`.  The envelope version
`RNCommutatorSimpleStatement` (`EnvelopeSplit.lean`) is the special case
`X ↦ Fin 2 × X`, `H ↦ envelopeK 2 H` (`EnvelopeSimpleBridge.lean`).

`isSimpleGroup_commutator_of_bracket` moves simplicity of the subgroup `⁅G, G⁆` of the ambient
group to the intrinsic `commutator ↥G`, via `Subgroup.map_subtype_commutator`.

*Truth.*  `Nontrivial X` is needed: for `X = Unit` the Cantor space is one point, `V_X(H)` is
trivial and a trivial group is not simple.  `2 ≤ card X` is the same as `Nontrivial X`.
Self-similarity is kept (it is Nekrashevych's hypothesis and is what fragments an element of
`H` acting on the whole tree into pieces with small support).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- **The commutator subgroup of a Röver–Nekrashevych group is simple.** -/
def RNCommutatorSimpleStatement' : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    IsSimpleGroup ↥(commutator ↥(roverNekrashevych X H))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNCommutatorSimpleStatement'

/-- Simplicity of `⁅G, G⁆ ≤ M` gives simplicity of the intrinsic commutator subgroup of `G`. -/
theorem isSimpleGroup_commutator_of_bracket {M : Type*} [Group M] (G : Subgroup M)
    (h : IsSimpleGroup ↥⁅G, G⁆) : IsSimpleGroup ↥(commutator ↥G) := by
  haveI := h
  exact (((commutator ↥G).equivMapOfInjective G.subtype G.subtype_injective).trans
    (MulEquiv.subgroupCongr G.map_subtype_commutator)).isSimpleGroup

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.isSimpleGroup_commutator_of_bracket

end GroupApproximation.BooneHigman.Metabelian.Envelope
