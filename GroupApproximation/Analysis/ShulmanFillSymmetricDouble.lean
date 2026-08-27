import GroupApproximation.Analysis.ShulmanSymmetricDoubleRoute
import GroupApproximation.Analysis.ShulmanFillConjugatePair
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

/-!
# Theorem 10 at a corona-valued model, reduced to one faithfulness statement

`ShulmanSymmetricDouble.SymmetricDoubleMFStatement` is Shulman's Theorem 10.
This module assembles it from a single named input, and records what the
corona vocabulary does and does not save.

## What the corona saves, and what it does not

In the paper the two asymptotic homomorphisms of the double are `φ⁽²⁾` and
`φ⁽¹⁾ = V* φ⁽²⁾ V`, where `V` is a Halmos dilation (Lemma 9) of a
quasicentrally corrected lift of the flip, and the commutation
`‖[V, φ_k(c) ⊕ φ_k(c)]‖ ≤ 1/k` is only approximate.  It is approximate because
`V` lives in `M₄(𝒟)` and has to converge `*`-strongly to the flip.

At a `D` already sitting inside a corona none of that is needed: the flip is
an *exact* unitary of `M₂` over the corona and commutes *exactly* with the
diagonal image of `C` (`Analysis/ShulmanFillSymmetricDoubleFlip`), so the
conjugated pair exists on the nose.  Lemma 9 is a device for producing an
approximately commuting unitary where an exact one is unavailable; in corona
vocabulary an exact one is available, and Lemma 9 drops out of the argument.

What does **not** drop out is faithfulness.  Shulman's Theorem 4 is what makes
the glued asymptotic homomorphism lift a *faithful* representation of the
double, and that is the only reason the resulting model is injective.  So the
corona reformulation concentrates the whole of Theorem 10 into the statement
below: the conjugated pair evaluates the double faithfully.

## A correction to the plan

The suggestion that `ShulmanContractiveAsymptoticLift.lift` supplies the
direction of Theorem 4 we need does not survive inspection.  That lemma
chooses bounded representatives of a map *into a corona* — it turns a corona
homomorphism into coordinate models.  Theorem 4 is a different statement: it
lifts an arbitrary `*`-homomorphism `D → B(H)` to a discrete asymptotic
homomorphism into `𝒟`, converging `*`-strongly to the given representation.
In the proof of Theorem 10 the representation being lifted is `ρ₂ = π₂ ⊕ π₁`,
built from a *faithful representation of the amalgam* `π = π₁ * π₂`, and
`π₁, π₂` are arbitrary representations of `D` on a Hilbert space, not
corona-valued maps.  The fact that `D` sits inside a corona says nothing about
where `π₁` and `π₂` take their values.  So Theorem 4 — or some other device
that produces a faithful evaluation — is genuinely needed, and it is exactly
what the statement below isolates.

This module is not in the root import list.  It was authored while builds were
suspended, so it is kept out of the closure until it has been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-- **The one input of Theorem 10 in corona vocabulary.**  For a separable MF
`D` and a subalgebra `C ⊆ D`, some faithful unital corona model of `D` and some
unitary of the corona commuting with the image of `C` evaluate the symmetric
double faithfully.

This is a sufficient condition, in the shape the paper's proof produces: its
`φ` is the corona model of `ρ₂` and its `V` is the (there approximate, here
exact) conjugating unitary.  Faithfulness is what Shulman's Theorem 4 supplies,
by making the glued asymptotic homomorphism lift a faithful representation of
the double. -/
def ConjugatedPairFaithfulStatement : Prop :=
  ∀ {C D : Type} [CStarAlgebra C] [CStarAlgebra D] (k : C →⋆ₐ[ℂ] D)
    [Nonempty (CStarAmalgamRepresentation k k)],
    IsMFAlgebra D →
      ∃ Z : ℕ → FiniteModel, ∃ hZ : ∀ n, Nonempty (Z n),
        letI : ∀ n, Nonempty (Z n) := hZ
        ∃ phi : D →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
          ∃ V : unitary (NormMatrixCStarCorona (fun n ↦ Z n)),
            ∃ hV : ∀ c : C,
                (V : NormMatrixCStarCorona (fun n ↦ Z n)) * phi (k c) =
                  phi (k c) * (V : NormMatrixCStarCorona (fun n ↦ Z n)),
              Function.Injective (universalCStarAmalgamEval k k
                (conjugateRepresentation k k phi phi rfl V hV))

open Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit in
/-- **Theorem 10 from that input.**  The carrier of a conjugated corona pair is
a norm corona, hence MF, and separability of the double comes from
separability of `D`, so faithfulness is the only thing left to supply. -/
theorem symmetricDoubleMF_of_conjugatedPairFaithful
    (hfaith : ConjugatedPairFaithfulStatement) :
    ShulmanSymmetricDouble.SymmetricDoubleMFStatement := by
  intro C D _ _ k _ hD
  obtain ⟨Z, hZ, phi, V, hV, hinj⟩ := hfaith k hD
  letI : ∀ n, Nonempty (Z n) := hZ
  haveI : TopologicalSpace.SeparableSpace D := hD.1
  exact isMFAlgebra_of_faithful_eval k k
    (conjugateRepresentation k k phi phi rfl V hV)
    (normMatrixCorona_hasMFEmbedding_of_positive Z hZ) hinj

/-- **Theorem 16 along Shulman's own route, from its three inputs.**  Theorem
13 embeds the amalgam in the symmetric double, Theorem 10 makes the double MF,
and MF passes backward along the embedding. -/
theorem isMFAlgebra_of_symmetricDoubleRoute
    (hdouble : ShulmanSymmetricDouble.SymmetricDoubleMFStatement)
    (hembed : ShulmanSymmetricDouble.AmalgamEmbedsSymmetricDoubleStatement)
    {C A₁ A₂ D : Type} [CStarAlgebra C] [CStarAlgebra A₁] [CStarAlgebra A₂]
    [CStarAlgebra D] (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
    (k : C →⋆ₐ[ℂ] D)
    (phiA : A₁ →⋆ₐ[ℂ] D) (phiB : A₂ →⋆ₐ[ℂ] D)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    [Nonempty (CStarAmalgamRepresentation k k)]
    (hC : TopologicalSpace.SeparableSpace C)
    (hphiA : Function.Injective phiA) (hphiB : Function.Injective phiB)
    (hkA : ∀ c : C, phiA (iA c) = k c) (hkB : ∀ c : C, phiB (iB c) = k c)
    (hDmf : IsMFAlgebra D) :
    IsMFAlgebra (UniversalCStarAmalgam iA iB) := by
  obtain ⟨e, he⟩ := hembed iA iB k phiA phiB hC hphiA hphiB hkA hkB
  exact ShulmanSymmetricDouble.isMFAlgebra_of_injective_into_symmetricDouble
    (hdouble k hDmf) e he

end

end ShulmanFill
end GroupApproximation
