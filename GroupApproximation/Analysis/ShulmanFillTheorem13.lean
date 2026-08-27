import GroupApproximation.Analysis.ShulmanFillSymmetricDoubleEmbedTheorem13

/-!
# Theorem 13: the shape Enders--Shulman's construction produces

LITERATURE INPUT: D. Enders and T. Shulman, *On the (Local) Lifting Property*,
arXiv:2403.12224, Theorem 4.11, cited as Theorem 13 of T. Shulman,
arXiv:2603.13564v2.

`Analysis/ShulmanFillSymmetricDoubleEmbedTheorem13` already carries the formal
half: the map `Φ = φ_A * φ_B` is `symmetricDoubleEmbedding` (the peer lane's
`factorAmalgamToSymmetricTarget` at `e = id`, with both generator formulas
`rfl`), `factorAmalgamToSymmetricTarget_eq_comp` factors the peer's map at a
general target as `e ∘ Φ`, and `injective_symmetricDoubleEmbedding_of_witness`
is step 5 of their proof — a map whose composite with something is injective is
injective.  Nothing here restates those.

What this module adds is the *shape* of the witness.  In Enders--Shulman the
target is not arbitrary: it is a compatible pair of representations of `(D, D)`
over `C`, namely `γ = (q ∘ Ad(1 ⊕ u) ∘ σ_A^{⊕∞}) * (q ∘ σ_B^{⊕∞})`.
`CompatibleTargetPairStatement` below is exactly that shape, and
`calkinWitness_of_compatibleTargetPair` proves the previously named
`CalkinWitnessStatement` from it through the universal property.  So the
remaining input mentions only a compatible pair, which is what the three
analytic theorems are used to build.

## The three atoms, and why they are not Props here

Their proof builds the pair in three steps:

1. **Arveson extension.**  `φ_A` is injective, so `α ∘ ι_A` transported to
   `φ_A(A) ⊆ D` is a ccp map into `B(H)`; Arveson extends it to a ccp map on
   all of `D`.
2. **Stinespring dilation.**  That ccp map dilates to a `*`-homomorphism
   `σ_A : D → B(K)`, and `φ_A(A)` lands in its multiplicative domain, so the
   compression recovers `α ∘ ι_A` on the nose.  Likewise `σ_B`.
3. **Voiculescu's theorem.**  Applied to
   `(σ_A φ_A ι_A)_{22} ⊕ (σ_A φ_A ι_A)^{⊕∞}` and the `B`-counterpart, it
   produces a unitary `u ∈ B(H^{⊕∞})` conjugating one to the other modulo
   `K(H)` — which is what makes the two legs agree on `C` in the Calkin
   quotient, so that they form a compatible pair.

None of the three is stated below as a named `Prop`, and that is deliberate.
Each is true only with `B(H)` as the target — Arveson needs an injective
target, Voiculescu needs the compacts — and the Calkin algebra is not
expressible yet.  A version of them abstracted over an arbitrary ambient
algebra and an arbitrary ideal would be *false*, and a false hypothesis is
worse than a missing one: it cannot be discharged, and it would silently make
every theorem standing on it vacuous.  So the three are recorded here in prose,
with their exact roles, and the one statement carried as a `Prop` is the
existence of the pair they build, which is an existence statement and so is at
worst hard.

What is and is not available, checked against the pinned Mathlib:

* `B(H)` **is** there.  `Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap`
  gives `CStarAlgebra (E →L[ℂ] E)` for a complex Hilbert space `E`, on top of
  `CStarRing (E →L[𝕜] E)` in `Mathlib/Analysis/InnerProductSpace/Adjoint`.
* The compact operators are there as a *submodule*, `compactOperator` in
  `Mathlib/Analysis/Normed/Operator/Compact/Basic`; they are not bundled as a
  closed two-sided ideal.
* The quotient is **not** there.  Mathlib carries no `CStarRing` instance on
  any quotient — the full list of its `CStarRing` instances is `ℝ`, `RCLike`,
  quaternions, products, pi types, `Eᵐᵒᵖ`, `CStarMatrix`, multipliers,
  unitizations, `E →L[𝕜] E`, `lp ∞`, and the various continuous-function
  algebras — and there is no `Analysis/CStarAlgebra/Quotient.lean`.

So the Calkin algebra needs its C-star structure built by hand, exactly as
this repository already builds the matrix corona's: the
`filterMatrixCoronaAlgebra*` instances of `Analysis/NormMatrixCorona` are that
same construction at a different quotient, and are the pattern to copy.  It is
a construction task of the same kind as the algebra `𝒟` of `*`-strongly
convergent matrix sequences that Theorem 10 needs.

This module is not in the root import list.  It was authored while builds were
suspended, so it is kept out of the closure until it has been elaborated.
-/

namespace GroupApproximation
namespace ShulmanSymmetricDouble

open MFAlgebraAmalgamCriterion

noncomputable section

/-- **The witness of Enders--Shulman, Theorem 4.11, in the shape their
construction produces it.**  The target is a compatible pair `(σ_A, σ_B)` of
representations of `D` agreeing on `γ(C)`, and the induced map on the
symmetric double detects the amalgam.

This is `CalkinWitnessStatement` with the target's structure exposed: their
`γ` is the pair `(q ∘ Ad(1 ⊕ u) ∘ σ_A^{⊕∞}, q ∘ σ_B^{⊕∞})`, whose two legs
agree on `C` precisely because Voiculescu's theorem supplied `u`. -/
def CompatibleTargetPairStatement : Prop :=
  ∀ {C A B D : Type} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra D] [Nontrivial D]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma),
      TopologicalSpace.SeparableSpace C →
      Function.Injective alpha → Function.Injective beta →
        ∃ T : Type, ∃ hTalg : CStarAlgebra T,
          letI : CStarAlgebra T := hTalg
          ∃ hTnt : Nontrivial T,
            letI : Nontrivial T := hTnt
            ∃ sigmaA : D →⋆ₐ[ℂ] T, ∃ sigmaB : D →⋆ₐ[ℂ] T,
              ∃ hsigma : sigmaA.comp gamma = sigmaB.comp gamma,
                Function.Injective
                  (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB
                    (universalCStarAmalgamEval gamma gamma
                      (CStarAmalgamRepresentation.ofCompatiblePair
                        gamma gamma sigmaA sigmaB hsigma)))

/-- The pair form of the witness implies the bare one: a compatible pair of
representations of `D` induces a `*`-homomorphism on the symmetric double, by
the universal property. -/
theorem calkinWitness_of_compatibleTargetPair
    (h : CompatibleTargetPairStatement) : CalkinWitnessStatement := by
  intro C A B D _ _ _ _ _ iA iB _ gamma alpha beta hA hB hC halpha hbeta
  obtain ⟨T, hTalg, hTnt, sigmaA, sigmaB, hsigma, hinj⟩ :=
    h iA iB gamma alpha beta hA hB hC halpha hbeta
  letI : CStarAlgebra T := hTalg
  haveI : Nontrivial T := hTnt
  exact ⟨T, hTalg, hTnt, _, hinj⟩

/-- **Theorem 13 from the pair witness.**  Composing with the reduction
already proved, `AmalgamEmbedsSymmetricDoubleStatement` — the form Shulman's
route consumes — follows from the existence of the compatible pair alone. -/
theorem amalgamEmbedsSymmetricDouble_of_compatibleTargetPair
    (h : CompatibleTargetPairStatement) :
    AmalgamEmbedsSymmetricDoubleStatement :=
  amalgamEmbedsSymmetricDouble_of_calkinWitness
    (calkinWitness_of_compatibleTargetPair h)

end

end ShulmanSymmetricDouble
end GroupApproximation
