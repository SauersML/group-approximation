import GroupApproximation.BooneHigman.Metabelian.EnvelopeFPStatement
import GroupApproximation.BooneHigman.Metabelian.EnvelopeFPFree
import GroupApproximation.BooneHigman.RNPresentation.SectionCriterion
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite presentation of `V_X(H)` from a normal-form section

`rnFinitelyPresented_of_freeSection` reduces `RNFinitelyPresentedStatement'` to
`RNFreeSectionStatement`.  The reduction feeds the surjection
`rnFreeHom H x₀ : V_X ∗ (H ∗ H) →* V_X(H)` (`EnvelopeFPFree.lean`) and the generating set
`rnFreeGenerators H` into `RNPresentation.isFinitelyPresented_of_section`.  The free product is
finitely presented by the Mathlib instance for `Monoid.Coprod` once `V_X` and `H` are.

*The isolated statement.*  `RNFreeSectionStatement` asks for two things.
1. Higman's theorem: `V_X` is finitely presented.
2. A normal form for `V_X(H)` modulo finitely many relators `R ⊆ ker (rnFreeHom H x₀)`.  This
   is a section `s : V_X(H) → (V_X ∗ (H ∗ H)) ⧸ ⟨⟨R⟩⟩` with `s 1 = 1` that intertwines right
   multiplication by the three factor images.  In the intended proof, `R` consists of Higman's
   relators, the commutation relators `[localize [x₀] h, v]` for `v` supported off `cone [x₀]`,
   and the splitting relators expressing `localize [x₀] h` through the states of `h`.

*Truth.*  Assume the target statement, Higman's theorem, and that `H` is finitely presented.
Then `K = V_X ∗ (H ∗ H)` is finitely presented and `rnFreeHom H x₀` is a surjection onto a
finitely presented group.  Its kernel is therefore the normal closure of a finite set `R`.  The
inverse of the induced isomorphism `K ⧸ ⟨⟨R⟩⟩ ≃* V_X(H)` is a section `s` with `s 1 = 1`, and
`s (v * φ k) = s v * s (φ k) = s v * k`.  So the statement is true.

*Why it is strictly smaller in proof content.*  The reduction below discharges all of the
following.
* The choice of presentation complex.
* That the Röver–Nekrashevych images of `V_X` and of `h ↦ h`, `h ↦ localize [x₀] h` lie in
  `V_X(H)`.
* Surjectivity: every `localize w h` is a `V_X`-conjugate of `localize [x₀] h`, by cone
  transitivity (`exists_mapsCone_of_ne_nil`, `MapsCone.conj_localize`).
* That the three factor images generate the free product.
* Finite presentability of the free product.
* The kernel-through-a-section argument.

What remains is the normal-form combinatorics inside the quotient, plus Higman's theorem.  The
case `H = ⊥` of the target is Higman's theorem, and no finite presentation of `V_X` exists in
the corpus, so the target cannot be closed from the present repository.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- **Normal-form section for the Röver–Nekrashevych presentation.**  `V_X` is finitely
presented, and for some one-letter cone `[x₀]` there are finitely many relators in the kernel of
`V_X ∗ (H ∗ H) →* V_X(H)` whose quotient carries a unital section intertwining right
multiplication by the factor generators. -/
def RNFreeSectionStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented ↥H →
      Group.IsFinitelyPresented ↥(higmanThompsonV X) ∧
        ∃ (x₀ : X) (R : Set (RNFree X H)), R.Finite ∧ R ⊆ (rnFreeHom H x₀).ker ∧
          ∃ s : ↥(roverNekrashevych X H) → RNFree X H ⧸ Subgroup.normalClosure R,
            s 1 = 1 ∧
              ∀ v : ↥(roverNekrashevych X H), ∀ k ∈ rnFreeGenerators H,
                s v * (k : RNFree X H ⧸ Subgroup.normalClosure R) = s (v * rnFreeHom H x₀ k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNFreeSectionStatement

/-- The normal-form section yields the finite presentation of `V_X(H)`. -/
theorem rnFinitelyPresented_of_freeSection (hsec : RNFreeSectionStatement) :
    RNFinitelyPresentedStatement' := by
  intro X _ _ H hH hfp
  obtain ⟨hV, x₀, R, hR, hRker, s, hs1, hmul⟩ := hsec X H hH hfp
  have : Group.IsFinitelyPresented (RNFree X H) := inferInstance
  exact RNPresentation.isFinitelyPresented_of_section (rnFreeHom H x₀)
    (rnFreeHom_surjective H x₀) R hR hRker (rnFreeGenerators H)
    (closure_rnFreeGenerators H) s hs1 hmul

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFinitelyPresented_of_freeSection

end GroupApproximation.BooneHigman.Metabelian.Envelope
