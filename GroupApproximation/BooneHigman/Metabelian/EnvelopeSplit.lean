import GroupApproximation.BooneHigman.Metabelian.EnvelopeSplitEmbed
import GroupApproximation.Meta.AxiomGuard

/-!
# Zaremsky's envelope, split into four facts about one Röver–Nekrashevych group

For a finite nontrivial `X` and `H ≤ Aut(T_X)`, set `Y = envelopeY X 2 = Fin 2 × X`,
`K = envelopeK 2 H` (the regrouped copy of `H`, `EnvelopeSplitEmbed.lean`) and
`V = envelopeV X H = roverNekrashevych Y K`.  With the binders of
`RoverNekrashevychEnvelopeStatement` (`H` self-similar and finitely presented):

* `RNFinitelyPresentedStatement`: `V` is finitely presented.
* `RNCommutatorFiniteIndexStatement`: `[V, V]` has finite index in `V`.
* `RNCommutatorSimpleStatement`: `[V, V]` is simple.
* `RNWreathEmbedStatement`: if `[V, V]` has finite index, then
  `[V, V] ≀ (V ⧸ [V, V])` embeds in `[V, V]` (Zaremsky, arXiv:2405.09722, Proposition 2.5).

`rnEnvelope_of_four` proves `RoverNekrashevychEnvelopeStatement` from the four, with the
witnesses `Y`, `K`, `envelopeHom 2 H` (injective by `envelopeHom_injective`).

Route: instantiate the existential with the concrete construction; each conjunct is one of the
four statements, and the wreath conjunct feeds the finite-index conjunct to the fourth.

*Truth.*  `K ≅ H` is self-similar and finitely presented (`isSelfSimilar_envelopeK`,
`isFinitelyPresented_envelopeK`).  `V` is finitely presented (Zaremsky, Section 3); `[V, V]` is
simple (Nekrashevych, Theorem 4.7); `|Y| = 2|X|` is even, so `V_Y` is perfect (Higman), every
localised `k ∈ K` splits into `2|X|` localised states whose `Fin 2`-copies coincide, so the
abelianisation `A` of `V` satisfies `A = 2A` and is finitely generated, hence finite;
Proposition 2.5 embeds `S ≀ F` in `S = [V, V]` for every finite group `F`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- The Röver–Nekrashevych group of the regrouped copy of `H`. -/
abbrev envelopeV (X : Type*) [Finite X] (H : Subgroup (TreeAut X)) :
    Subgroup (Equiv.Perm (Cantor (envelopeY X 2))) :=
  roverNekrashevych (envelopeY X 2) (envelopeK 2 H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.envelopeV

/-- `V_{Fin 2 × X}(K)` is finitely presented. -/
def RNFinitelyPresentedStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented H → Group.IsFinitelyPresented ↥(envelopeV X H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNFinitelyPresentedStatement

/-- The commutator subgroup of `V_{Fin 2 × X}(K)` has finite index. -/
def RNCommutatorFiniteIndexStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented H → (commutator ↥(envelopeV X H)).FiniteIndex

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNCommutatorFiniteIndexStatement

/-- The commutator subgroup of `V_{Fin 2 × X}(K)` is simple. -/
def RNCommutatorSimpleStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented H → IsSimpleGroup ↥(commutator ↥(envelopeV X H))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNCommutatorSimpleStatement

/-- Zaremsky's Proposition 2.5 for `S = [V, V]`, `V = V_{Fin 2 × X}(K)`: when `S` has finite
index, `S ≀ (V ⧸ S)` embeds in `S`. -/
def RNWreathEmbedStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented H → (commutator ↥(envelopeV X H)).FiniteIndex →
      ∃ j : RegularWreath ↥(commutator ↥(envelopeV X H))
          (↥(envelopeV X H) ⧸ commutator ↥(envelopeV X H)) →*
            ↥(commutator ↥(envelopeV X H)),
        Function.Injective j

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNWreathEmbedStatement

/-- The four Röver–Nekrashevych facts give `RoverNekrashevychEnvelopeStatement`. -/
theorem rnEnvelope_of_four (hfp : RNFinitelyPresentedStatement)
    (hfi : RNCommutatorFiniteIndexStatement) (hs : RNCommutatorSimpleStatement)
    (hw : RNWreathEmbedStatement) : RoverNekrashevychEnvelopeStatement := by
  intro X _ _ H hH hHfp
  exact ⟨envelopeY X 2, inferInstance, inferInstance, envelopeK 2 H, envelopeHom 2 H,
    envelopeHom_injective H, hfp X H hH hHfp, hfi X H hH hHfp, hs X H hH hHfp,
    hw X H hH hHfp (hfi X H hH hHfp)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnEnvelope_of_four

end GroupApproximation.BooneHigman.Metabelian.Envelope
