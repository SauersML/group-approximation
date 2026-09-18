import GroupApproximation.BooneHigman.Metabelian.EnvelopeFPSection
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting the normal-form section statement: Higman's theorem and the core

`RNFreeSectionStatement` (`EnvelopeFPSection.lean`) is a conjunction.
1. Higman's theorem: `V_X` is finitely presented.
2. The normal form for `V_X(H)` modulo finitely many relators in `V_X ∗ (H ∗ H)`.

This module names the two conjuncts separately.
* `HigmanVFPStatement`: `V_X = higmanThompsonV X` is finitely presented for every finite
  nontrivial alphabet `X`.
* `RNFreeSectionCoreStatement`: `RNFreeSectionStatement` with the `V_X` conjunct removed.

`rnFreeSection_of_higmanV_core` puts them back together.

*Truth.*  `higmanThompsonV X` is the group of permutations of `ℕ → X` that act as prefix
substitutions on all cones of some fixed depth.  This is the Higman–Thompson group `V_{|X|,1}`.
A depth-`N` table maps the `|X|^N` depth-`N` cones bijectively onto the cones of a complete
prefix code.  Conversely, a bijection between two complete prefix codes refines to a depth-`N`
table once `N` bounds the lengths in the domain code.  Higman (1974) proved that `V_{d,1}` is
finitely presented for every `d ≥ 2`, so `HigmanVFPStatement` is true.
`RNFreeSectionCoreStatement` is a weakening of `RNFreeSectionStatement`, whose truth is argued
in `EnvelopeFPSection.lean`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- **Higman's theorem for `V_{|X|,1}`.**  The Higman–Thompson group over a finite alphabet
with at least two letters is finitely presented. -/
def HigmanVFPStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X], Group.IsFinitelyPresented ↥(higmanThompsonV X)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVFPStatement

/-- **Core of the normal-form section.**  This is `RNFreeSectionStatement` without Higman's
theorem.  For some one-letter cone `[x₀]`, finitely many relators lie in the kernel of
`V_X ∗ (H ∗ H) →* V_X(H)`, and their quotient carries a unital section that intertwines right
multiplication by the factor generators. -/
def RNFreeSectionCoreStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented ↥H →
      ∃ (x₀ : X) (R : Set (RNFree X H)), R.Finite ∧ R ⊆ (rnFreeHom H x₀).ker ∧
        ∃ s : ↥(roverNekrashevych X H) → RNFree X H ⧸ Subgroup.normalClosure R,
          s 1 = 1 ∧
            ∀ v : ↥(roverNekrashevych X H), ∀ k ∈ rnFreeGenerators H,
              s v * (k : RNFree X H ⧸ Subgroup.normalClosure R) = s (v * rnFreeHom H x₀ k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNFreeSectionCoreStatement

/-- Higman's theorem together with the core normal form gives the normal-form section
statement. -/
theorem rnFreeSection_of_higmanV_core (hV : HigmanVFPStatement)
    (hcore : RNFreeSectionCoreStatement) : RNFreeSectionStatement := by
  intro X _ _ H hH hfp
  exact ⟨hV X, hcore X H hH hfp⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeSection_of_higmanV_core

end GroupApproximation.BooneHigman.Metabelian.Envelope
