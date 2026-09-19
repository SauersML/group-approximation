import GroupApproximation.Analysis.ShulmanFillTheorem13
import GroupApproximation.Analysis.ShulmanFillUnitalCorner

/-!
# Does the Calkin witness get cheaper when `D` already sits in a corona?

In Theorem 16's use `D = C*(l(A₁), r(A₂))` is a subalgebra of a norm matrix
corona `Q`, and `l`, `r` are faithful and compatible on `C`.  The question is
whether `CalkinWitnessStatement` can be discharged there without Voiculescu.

**It cannot, and the failure is exact.**  The witness asks for a compatible
pair `(σ_A, σ_B)` of representations of `D` agreeing on `γ(C)` such that

  `(σ_A ∘ α) * (σ_B ∘ β) : A *_C B → E`

is injective.  That map is `e ∘ Φ`, where `Φ = symmetricDoubleEmbedding` and
`e` is the evaluation of the double `D *_C D` at the pair.  Injectivity of a
composite needs both factors, and the two factors are exactly the two
literature inputs:

* `e` injective is Theorem 10's `ConjugatedPairFaithfulStatement` — the
  conjugated corona pair evaluates the *double* faithfully;
* `Φ` injective is Theorem 13.

The universal property supplies the map and nothing else; faithfulness of the
models bounds `e` from below and says nothing about `Φ`.  Taking the obvious
pair — `σ_A = σ_B =` the inclusion `D ⊆ Q`, so `σ_A α = l` and `σ_B β = r` —
gives the evaluation at the *given* corona pair, which is in general not
injective; that failure is the whole reason the double is introduced.  Nor does
the flip help by itself: the flip makes `ρ₁ = π₁ ⊕ π₂` and `ρ₂ = π₂ ⊕ π₁`
conjugate and equal on `C`, but `π₁` and `π₂` are representations of `D`
obtained from a faithful representation of the *double*, so the flip
construction presupposes `e` and still says nothing about `Φ`.

What Theorem 13 adds, and what no corona bookkeeping supplies, is that an
*arbitrary* compatible pair for `(A, B)` is dominated by one of the special
form `(ρ₁ α, ρ₂ β)`.  Getting there means extending a representation of `A` to
one of `D`, which is Arveson plus Stinespring, and then making the two
extensions agree on `C`, which is Voiculescu.  So the two inputs do not
collapse into `ConjugatedPairFaithfulStatement`.

## What does collapse

Something weaker collapses, and it is worth naming.  A compatible pair for
`(A, B)` with corona carrier that is faithful *on the amalgam* gives Theorem 16
outright, with no double, no Theorem 10 and no Theorem 13:
`shulmanTheorem16_of_faithfulPair` below.  The converse also holds, modulo the
support-corner unitalization already landed in
`Analysis/CompatibleCoronaSupportCorner`, because an MF amalgam's corona
embedding splits into its two factor legs.  So
`FaithfulCompatibleCoronaPairStatement` is Theorem 16 *restated*, not reduced:
naming it renames the debt rather than shrinking it.  Both routes are
strategies for building such a pair — the norming route builds a whole family
and takes a reduced product, Shulman's route builds one through the double.

And the two symmetric-double inputs are not independent:
`symmetricDoubleMF_of_shulmanTheorem16` below derives Theorem 10 from Theorem
16, by taking `A₁ = A₂ = D` with the inclusion pair.  So on that route the only
strengthening over the endpoint is Theorem 13, and Theorem 10 is a corollary of
what it is being used to prove.

That last point is about the *debt order*, not about a proof route.  The
implication runs from the endpoint, so it cannot be used to prove Theorem 10:
a non-circular proof of Theorem 16 along this route still has to prove Theorem
10 on Shulman's own terms, by his Theorem 4 together with the flip, which is
the work `Analysis/ShulmanFillSymmetricDouble` is doing.  What the implication
does say is that carrying `symmetricDoubleMF` as a named unresolved premise can never
overstate the debt, since the endpoint already implies it.

So the honest bottom of the lane is a choice between two pieces of
construction-and-proof work: build `𝒟`, and `B(H)`'s compacts and Calkin
quotient if they turn out to be expressible, and prove Theorem 4 and Theorem
13's Voiculescu step; or discharge the norming atom.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

open Manuscript.MFRecognition

noncomputable section

/-- **One faithful compatible pair.**  Under the hypotheses of the printed
criterion, some compatible representation with an MF carrier evaluates the
amalgam faithfully.  This is the norming input with the family collapsed to a
single member and the approximation replaced by faithfulness. -/
def FaithfulCompatibleCoronaPairStatement : Prop :=
  ∀ {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁]
    [CStarAlgebra A₂] (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
    [Nonempty (CStarAmalgamRepresentation iA iB)],
      TopologicalSpace.SeparableSpace C →
      TopologicalSpace.SeparableSpace A₁ →
      TopologicalSpace.SeparableSpace A₂ →
      ∀ (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
        (phiA : A₁ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
        (phiB : A₂ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)),
        Function.Injective phiA → Function.Injective phiB →
          (∀ c : C, phiA (iA c) = phiB (iB c)) →
            ∃ R : CStarAmalgamRepresentation iA iB,
              HasMFEmbedding R.carrier ∧
                Function.Injective (universalCStarAmalgamEval iA iB R)

/-- **Theorem 16 from one faithful pair**, with no double and no embedding
step. -/
theorem shulmanTheorem16_of_faithfulPair
    (hpair : FaithfulCompatibleCoronaPairStatement) :
    HNNPermanence.ShulmanTheorem16Statement := by
  intro C A₁ A₂ _ _ _ iA iB _ hC hA₁ hA₂ Y _ phiA phiB hphiA hphiB hcomp
  haveI : TopologicalSpace.SeparableSpace A₁ := hA₁
  haveI : TopologicalSpace.SeparableSpace A₂ := hA₂
  obtain ⟨R, hRMF, hRfaithful⟩ :=
    hpair iA iB hC hA₁ hA₂ Y phiA phiB hphiA hphiB hcomp
  exact isMFAlgebra_of_faithful_eval iA iB R hRMF hRfaithful

/-- **Theorem 10 is a corollary of Theorem 16.**  Apply the printed criterion
with both factors equal to `D` and both corona embeddings equal to the one
supplied by `D`'s MF property; the compatibility condition is then reflexivity,
and the conclusion is that the symmetric double is MF.

The separability of `C` is the printed criterion's hypothesis; Shulman's
Theorem 10 does not ask for it, so this is the separable case of it, which is
the case the recognition chain uses. -/
theorem symmetricDoubleMF_of_shulmanTheorem16
    (h16 : HNNPermanence.ShulmanTheorem16Statement)
    {C D : Type} [CStarAlgebra C] [CStarAlgebra D] (k : C →⋆ₐ[ℂ] D)
    [Nonempty (CStarAmalgamRepresentation k k)]
    (hC : TopologicalSpace.SeparableSpace C) (hD : IsMFAlgebra D) :
    IsMFAlgebra (UniversalCStarAmalgam k k) := by
  obtain ⟨X, hXne, _, _, e, he⟩ := hD.2
  letI : ∀ n, Nonempty (X n) := hXne
  exact h16 k k hC hD.1 hD.1 X e e he he fun _ ↦ rfl

end

end ShulmanFill
end GroupApproximation
