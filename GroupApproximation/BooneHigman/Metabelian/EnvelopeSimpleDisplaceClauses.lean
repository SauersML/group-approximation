import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleGap
import GroupApproximation.Meta.AxiomGuard

/-!
# The three clauses of `RNDisplaceCompressStatement`

`RNDisplaceCompressStatement` (in `EnvelopeSimpleGap`) is the conjunction of three clauses about
`V = roverNekrashevych X H`.  This file states each clause verbatim as its own `Prop`, so that the
clauses can be proved independently, and proves the splitting theorem
`rnDisplaceCompress_of_clauses`.

* `RNDisplaceStatement`: nontrivial elements of `⁅V, V⁆` displace some cone.
* `RNCompressStatement`: `⁅V, V⁆` compresses sets missing a cone into `cone (u ++ [a, a])`.
* `RNFragmentsStatement`: `V` fragments into pieces jointly supported in sets missing a cone.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement
open Trees

/-- **Displacement** (clause (D) of `RNDisplaceCompressStatement`). -/
def RNDisplaceStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    ∀ f ∈ ⁅roverNekrashevych X H, roverNekrashevych X H⁆, f ≠ 1 →
      ∃ u : List X, Disjoint (f '' cone u) (cone u)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNDisplaceStatement

/-- **Compression** (clause (C) of `RNDisplaceCompressStatement`). -/
def RNCompressStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    ∀ (u : List X) (a : X),
      Compressible (roverNekrashevych X H) (cone (u ++ [a, a])) MissesCone

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNCompressStatement

/-- **Fragmentation** (clause (F) of `RNDisplaceCompressStatement`). -/
def RNFragmentsStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Fragments (roverNekrashevych X H) MissesCone

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNFragmentsStatement

/-- The three clauses give `RNDisplaceCompressStatement`. -/
theorem rnDisplaceCompress_of_clauses (hD : RNDisplaceStatement) (hC : RNCompressStatement)
    (hF : RNFragmentsStatement) : RNDisplaceCompressStatement := by
  intro X _ _ H hH
  exact ⟨hD X H hH, hC X H hH, hF X H hH⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnDisplaceCompress_of_clauses

end GroupApproximation.BooneHigman.Metabelian.Envelope
