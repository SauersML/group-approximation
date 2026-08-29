import GroupApproximation.Analysis.ShulmanFillNormingAmalgamWitness
import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftFaithful
import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftPrinted
import GroupApproximation.Analysis.ShulmanFillNormingFactorMapRange
import GroupApproximation.Analysis.ShulmanFillTheorem13
import GroupApproximation.Analysis.ShulmanSymmetricDoubleRoute

/-!
# Shulman's Theorem 10 from the printed package and Gelfand--Naimark

`Analysis/ShulmanFillNormingExistentialLiftPrinted` derives Theorem 10 from
`Theorem4PrintedPairStatement` **given a faithful pair of representations on a
separable Hilbert space**.  `ShulmanSymmetricDouble.SymmetricDoubleMFStatement`
asks for Theorem 10 with no such pair handed in, so the pair has to be produced,
and producing it is exactly Gelfand--Naimark for the symmetric double.

## The assembly

With `D` separable MF and `k : C →⋆ₐ[ℂ] D`, the double `D *_C D` is separable
(`separableSpace_universalCStarAmalgam`) and nontrivial
(`nontrivial_universalCStarAmalgam`), so `SeparableFaithfulRepresentationStatement`
gives a faithful `π : D *_C D →⋆ₐ[ℂ] B(H)` on a separable `H`.  Put
`ρ₁ = π ∘ ι₁` and `ρ₂ = π ∘ ι₂` for the two canonical maps.  Then

* `ρ₁` and `ρ₂` are faithful, because `ι₁` and `ι₂` are — and they are, for a
  *symmetric* double, by `injective_universalCStarAmalgamLeft_symmetric`: the
  identity pair `(id, id)` is a compatible representation of `D *_C D` on `D`
  itself, and `universalCStarAmalgamLeft_injective_of_coordinate` reads the
  injectivity off it;
* they agree on `C`, by `universalCStarAmalgam_compatible`;
* and the faithfulness `isMFAlgebra_amalgam_of_printedPair` asks of the glued
  limit is faithfulness of `π` itself, because
  `eval_limitRep_eq_of_comp` identifies the evaluation at `limitRep k hρ` with
  `π` — both are `*`-homomorphisms out of the double agreeing on the two factor
  images, so the uniqueness half of the universal property identifies them.

The three nontriviality instances the printed route needs are all read off `π`:
`H →L[ℂ] H` is nontrivial because a nontrivial algebra embeds in it, and
`B(H ⊕ H)` because `hBlockOp` is injective
(`Analysis/ShulmanFillNormingExistentialLiftFaithful.hBlockOp_injective`).

## What is still cited rather than proved

`SeparableFaithfulRepresentationStatement` — Gelfand--Naimark on a separable
Hilbert space.  This is a standard theorem that is simply not in the tree.  It
is not in Mathlib at the pinned revision either: there is no `GelfandNaimark`
anywhere in it, and no statement of the form
`∃ f : A →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective f`.  What the repository does
have is the per-state half of the construction, in
`Analysis/CStarStateGNS`: `State.GNSSpace`, `State.gnsRep`, `State.gnsVector`,
`State.norm_gnsRep_apply_le`, and `eq_zero_of_forall_state_inner_eq_zero`, which
says the states separate points.  What is missing is the assembly — the direct
sum of the GNS representations over a family of states that separates points,
together with the countable choice of such a family that keeps the resulting
Hilbert space separable.  Neither step is deep; neither is written.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology MFAlgebraAmalgamCriterion

noncomputable section

universe w

/-! ## Gelfand--Naimark, as a named input -/

/-- **A separable C-star algebra has a faithful representation on a separable
Hilbert space.**  Gelfand--Naimark, restricted to what the recognition route
uses.

This is cited, not proved.  It is absent from Mathlib at the pinned revision,
and the repository has only the per-state half of the construction in
`Analysis/CStarStateGNS`; the direct sum over a separating family of states, and
the countable choice of such a family, are the missing steps.

The algebra is left in its own universe and the Hilbert space is not.  That
asymmetry is the statement, not a convenience: the one algebra this is applied
to is `UniversalCStarAmalgam gamma gamma`, which lies one universe above `C` and
`D` — it is a subalgebra of a product indexed by a `Type`-valued structure — while
the *conclusion* is about a **separable** Hilbert space, and a separable Hilbert
space is `ℓ²(ℕ)` up to isomorphism, which lives in `Type`.  So `H : Type` is what
Gelfand--Naimark actually delivers here, and it is also what
`Theorem4PrintedPairStatement` consumes.  No universe descent is being smuggled
in: nothing is shrunk, the large algebra simply acts on a small space.  Consumers
must pin the universe — `SeparableFaithfulRepresentationStatement.{1}` below —
or each occurrence picks up its own. -/
def SeparableFaithfulRepresentationStatement : Prop :=
  ∀ (B : Type w) [CStarAlgebra B] [Nontrivial B]
    [TopologicalSpace.SeparableSpace B],
    ∃ (H : Type) (hgroup : NormedAddCommGroup H),
      letI : NormedAddCommGroup H := hgroup
      ∃ hinner : InnerProductSpace ℂ H,
        letI : InnerProductSpace ℂ H := hinner
        ∃ (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
          (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective π

/-! ## The canonical maps of a symmetric double are faithful -/

section Symmetric

variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D] [Nontrivial D]
variable (k : C →⋆ₐ[ℂ] D) [Nonempty (CStarAmalgamRepresentation k k)]

/-- The identity pair is a compatible representation of a symmetric double on
its own factor. -/
def identityPairRepresentation : CStarAmalgamRepresentation k k :=
  CStarAmalgamRepresentation.ofCompatiblePair k k
    (StarAlgHom.id ℂ D) (StarAlgHom.id ℂ D) rfl

/-- **The left canonical map of a symmetric double is faithful.**  Read off the
identity pair, whose left leg is the identity. -/
theorem injective_universalCStarAmalgamLeft_symmetric :
    Function.Injective (universalCStarAmalgamLeft k k) :=
  universalCStarAmalgamLeft_injective_of_coordinate k k
    (identityPairRepresentation k) fun _ _ h ↦ h

/-- **The right canonical map of a symmetric double is faithful.** -/
theorem injective_universalCStarAmalgamRight_symmetric :
    Function.Injective (universalCStarAmalgamRight k k) :=
  universalCStarAmalgamRight_injective_of_coordinate k k
    (identityPairRepresentation k) fun _ _ h ↦ h

end Symmetric

/-! ## The glued limit of a pair of legs is the representation itself -/

section Limit

variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable (k : C →⋆ₐ[ℂ] D) [Nonempty (CStarAmalgamRepresentation k k)]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]

/-- **The evaluation at the pair of legs of `π` is `π`.**  Both sides are
`*`-homomorphisms out of the double sending the left factor to `π ∘ ι₁` and the
right to `π ∘ ι₂`, so the uniqueness half of the universal property identifies
them.  This is what turns the faithfulness hypothesis of
`isMFAlgebra_amalgam_of_printedPair` into faithfulness of `π`. -/
theorem eval_limitRep_eq_of_comp
    (π : UniversalCStarAmalgam k k →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hρ : (π.comp (universalCStarAmalgamLeft k k)).comp k
      = (π.comp (universalCStarAmalgamRight k k)).comp k)
    (x : UniversalCStarAmalgam k k) :
    universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ) x
      = π x := by
  obtain ⟨f, _hf, huniq⟩ :=
    universalCStarAmalgam_existsUnique_lift k k
      (π.comp (universalCStarAmalgamLeft k k))
      (π.comp (universalCStarAmalgamRight k k)) hρ
  have hleft := huniq
    (universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hright := huniq π ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact DFunLike.congr_fun (hleft.trans hright.symm) x

end Limit

/-! ## Theorem 10 -/

/-- **Shulman's Theorem 10 from the printed package and Gelfand--Naimark.**  No
faithful pair has to be handed in: it is produced from a faithful representation
of the double, whose two legs are faithful because the canonical maps of a
symmetric double are, and whose faithfulness *is* the hypothesis the printed
route asks of the glued limit.

The `∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)` binder is the one
`Analysis/ShulmanFillNormingEllTwoModels` carries throughout; it is true and a
caller discharges it by `inferInstance`. -/
theorem symmetricDoubleMF_of_printedPair
    [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
    (hT4 : Theorem4PrintedPairStatement)
    (hGNS : SeparableFaithfulRepresentationStatement.{1}) :
    ShulmanSymmetricDouble.SymmetricDoubleMFStatement := by
  intro C D _ _ k _ hDmf
  haveI : TopologicalSpace.SeparableSpace D := hDmf.1
  haveI : Nontrivial D := nontrivial_left_of_nonempty_representation k k
  haveI : TopologicalSpace.SeparableSpace (UniversalCStarAmalgam k k) :=
    separableSpace_universalCStarAmalgam k k
  haveI : Nontrivial (UniversalCStarAmalgam k k) :=
    nontrivial_universalCStarAmalgam k k
  obtain ⟨H, hgroup, hinner, hcomplete, hsep, π, hπ⟩ :=
    hGNS (UniversalCStarAmalgam k k)
  letI : NormedAddCommGroup H := hgroup
  letI : InnerProductSpace ℂ H := hinner
  haveI : CompleteSpace H := hcomplete
  haveI : TopologicalSpace.SeparableSpace H := hsep
  -- Nontriviality of the two operator algebras, read off `π` and `hBlockOp`.
  haveI : Nontrivial (H →L[ℂ] H) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (UniversalCStarAmalgam k k)
    exact ⟨⟨π a, π b, fun h ↦ hab (hπ h)⟩⟩
  haveI : Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2) := by
    obtain ⟨X, Y, hXY⟩ :=
      exists_pair_ne (CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))
    exact ⟨⟨hBlockOp X, hBlockOp Y, fun h ↦ hXY (hBlockOp_injective h)⟩⟩
  -- The two legs.
  have hρ : ((π.comp (universalCStarAmalgamLeft k k)).comp k)
      = ((π.comp (universalCStarAmalgamRight k k)).comp k) := by
    exact congrArg π.comp (universalCStarAmalgam_compatible k k)
  refine isMFAlgebra_amalgam_of_printedPair k hT4 hDmf
    (π.comp (universalCStarAmalgamLeft k k))
    (π.comp (universalCStarAmalgamRight k k))
    (hπ.comp (injective_universalCStarAmalgamLeft_symmetric k))
    (hπ.comp (injective_universalCStarAmalgamRight_symmetric k)) hρ ?_
  intro x y hxy
  apply hπ
  exact (eval_limitRep_eq_of_comp k π hρ x).symm.trans
    (hxy.trans (eval_limitRep_eq_of_comp k π hρ y))

/-! ## Theorem 13's witness, at every faithful target -/

/-- **The witness hypothesis of `shulmanTheorem16_of_typeZeroWitness`, from the
compatible-pair form of Theorem 13.**

The two differ in one quantifier.  `CompatibleTargetPairStatement` produces a
single target `T` with a compatible pair of representations on it, and asserts
that the factor map into `T` separates.  `shulmanTheorem16_of_typeZeroWitness`
asks for the factor map into *every* faithful `Type`-valued image of the double.
`MFAlgebraAmalgamCriterion.injective_factorAmalgamToSymmetricTarget_of_injective_target`
of `Analysis/ShulmanFillNormingFactorMapRange` closes the gap, and note that it
asks nothing of the produced target beyond the injectivity of its own factor
map — which is all Enders--Shulman claim, since
their `T` is an evaluation at a compatible pair and is not asserted to be
faithful. -/
theorem factorMapInjective_of_compatibleTargetPair
    (hCTP : ShulmanSymmetricDouble.CompatibleTargetPairStatement) :
    ∀ {C A B D : Type} [CStarAlgebra C] [CStarAlgebra A]
      [CStarAlgebra B] [CStarAlgebra D] [Nontrivial D]
      [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
      (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
      [Nonempty (CStarAmalgamRepresentation iA iB)]
      (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
      (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma),
        TopologicalSpace.SeparableSpace C →
        Function.Injective alpha → Function.Injective beta →
          ∀ (E : Type) (_ : CStarAlgebra E) (_ : Nontrivial E)
            (g : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E),
            Function.Injective g →
              Function.Injective (factorAmalgamToSymmetricTarget iA iB gamma
                alpha beta hA hB g) := by
  intro C A B D _ _ _ _ _ _ _ iA iB _ gamma alpha beta hA hB hC halpha hbeta E instE
    ntE g hg
  letI : CStarAlgebra E := instE
  haveI : Nontrivial E := ntE
  obtain ⟨T, hTalg, hTnt, sigmaA, sigmaB, hsigma, hinj⟩ :=
    hCTP iA iB gamma alpha beta hA hB hC halpha hbeta
  letI : CStarAlgebra T := hTalg
  haveI : Nontrivial T := hTnt
  exact injective_factorAmalgamToSymmetricTarget_of_injective_target
    iA iB gamma alpha beta hA hB _ hinj g hg

/-! ## The recognition debt, from three cited inputs -/

/-- **`ConjugateWordNormingStatement` from exactly three binders.**

Everything else on the route is proved.  The three are:

* `Theorem4PrintedPairStatement` — Shulman's Theorem 4, Remark 6 and Lemma 9 as
  one package at the printed models, which gives Theorem 10 through
  `symmetricDoubleMF_of_printedPair`;
* `ShulmanSymmetricDouble.CompatibleTargetPairStatement` — Enders--Shulman's
  Theorem 4.11, which gives the witness through
  `factorMapInjective_of_compatibleTargetPair`;
* `SeparableFaithfulRepresentationStatement` — Gelfand--Naimark on a separable
  Hilbert space, which produces the faithful pair Theorem 10 is applied to.

The first two are what the manuscript cites.  The third is a standard theorem
that is simply not in the tree, and not in Mathlib at the pinned revision
either; see its docstring above for exactly which half of the GNS construction
`Analysis/CStarStateGNS` already has. -/
theorem conjugateWordNorming_of_printedPair_of_compatible
    [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
    (hT4 : Theorem4PrintedPairStatement)
    (hCTP : ShulmanSymmetricDouble.CompatibleTargetPairStatement)
    (hGNS : SeparableFaithfulRepresentationStatement.{1}) :
    ConjugateWordNormingStatement :=
  conjugateWordNorming_of_typeZeroWitness
    (symmetricDoubleMF_of_printedPair hT4 hGNS)
    (factorMapInjective_of_compatibleTargetPair hCTP)

end

end ShulmanFill
end GroupApproximation
