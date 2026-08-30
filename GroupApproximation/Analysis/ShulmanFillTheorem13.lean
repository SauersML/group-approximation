import GroupApproximation.Analysis.ShulmanFillSymmetricDoubleEmbedTheorem13
import GroupApproximation.Analysis.ShulmanFillCalkinCompatibility

/-!
# Theorem 13: the shape Enders--Shulman's construction produces

The statement carried here is Theorem 4.11 of D. Enders and T. Shulman, *On
the (Local) Lifting Property*, arXiv:2403.12224, which T. Shulman,
arXiv:2603.13564v2, cites as Theorem 13.  It is carried as a `Prop` and
discharged nowhere in this repository; the citation records whose theorem it
is, not a licence to assume it.

`Analysis/ShulmanFillSymmetricDoubleEmbedTheorem13` used to carry a formal
half: the map `Φ = φ_A * φ_B` as `symmetricDoubleEmbedding`, the factorisation
of the peer's map through it, and step 5 of Enders--Shulman's proof.  All of
that has been **deleted**: `Φ` cannot be typed, because
`MFAlgebraAmalgamCriterion.factorAmalgamToSymmetricTarget` fixes its target in
`Type` while `UniversalCStarAmalgam gamma gamma` lies one universe up.  That
module's docstring records the obstruction in full.

What survives here is the *shape of the witness*.  In Enders--Shulman the
target is not arbitrary: it is a compatible pair of representations of
`(D, D)` over `C`, namely
`γ = (q ∘ Ad(1 ⊕ u) ∘ σ_A^{⊕∞}) * (q ∘ σ_B^{⊕∞})`.
`CompatibleTargetPairStatement` below is exactly that shape, and
`calkinWitness_of_compatibleTargetPair` proves the previously named
`CalkinWitnessStatement` from it through the universal property.  Both include
the factor-map injectivity furnished by the `(1,1)`-corner, hence both encode
all five proof steps; the difference is that the former exposes the compatible
pair.  Both are well-typed because their targets are already in `Type`.

`amalgamEmbedsSymmetricDouble_of_compatibleTargetPair` has been deleted with
the rest of the void chain.  Neither statement here is sufficient for the MF
conclusion on its own — each supplies *one* target, chosen by whoever
discharges it, whereas MF-ness of the amalgam needs an MF-embeddable target,
and the paper's is the Calkin algebra, which is not stably finite.  The
operative input is the `∀`-form in
`Analysis/ShulmanFillNormingAmalgamWitness`, which says the factor map is
faithful at *every* faithful `Type`-valued target — that is "`Φ` is injective"
stated without naming `Φ`, and it is what Enders--Shulman's argument actually
delivers.

Conversely, `compatibleTargetPair_of_calkinWitness` restricts the bare
target map to the two canonical copies of `D`; uniqueness in the universal
property identifies the map induced from those restrictions with the original
one.  Hence `compatibleTargetPair_iff_calkinWitness` proves that the two
well-typed interfaces are exactly equivalent.  This closes the statement-
normalization seam, not the analytic existence theorem itself.

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

None of the three is stated below as a named `Prop`.  Each is true only with
`B(H)` as the target — Arveson needs an injective target, Voiculescu needs the
compacts — and a version of them abstracted over an arbitrary ambient algebra
and an arbitrary ideal would be *false*, and a false hypothesis is worse than a
missing one: it cannot be discharged, and it would silently make every theorem
standing on it vacuous.  So the three are recorded here in prose, with their
exact roles, and the one statement carried as a `Prop` is the existence of the
pair they build, which is an existence statement and so is at worst hard.

An earlier version of this paragraph gave a second reason, that the Calkin
algebra was not expressible.  That reason no longer holds, and the record of
what is available was wrong on two further counts.  Checked against the tree:

* `B(H)` **is** in Mathlib.  `Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap`
  gives `CStarAlgebra (E →L[ℂ] E)` for a complex Hilbert space `E`.
* The compact operators are in Mathlib only as a *submodule*; the closed
  two-sided ideal is `Analysis/CalkinCompactIdeal.compactIdeal`, and it is
  star-stable by Schauder's theorem, proved in
  `Analysis/CalkinSchauderProof.compactStarClosed`.
* The quotient C-star structure is **not** in Mathlib but **is** in this
  repository, root-imported and elaborated:
  `Analysis/CStarIdealApproximateUnit` constructs the approximate unit of any
  closed star-stable two-sided ideal and with it
  `CStarTensor.instCStarAlgebraQuotient`.  `Analysis/CalkinCStarAlgebra`
  assembles the two, so `Q(H)` is a C-star algebra with no hypothesis.
* **Stinespring's dilation theorem is in this repository** and root-imported:
  `Analysis/CStarStinespringHom.stinespringRepHom`, with the compression
  identity `stinespring_dilation_repHom`.
* **Arveson's extension theorem is in this repository at a separable `B(H)`
  target.**
  `Analysis/LanceMatrixArveson.exists_ucp_extension` is the matrix case, and
  `Analysis/ArvesonBHTarget.arvesonBH_of_limit` builds the `B(H)` case from it
  by compression and dilation along an exhausting family of isometries; its
  one owed input, the limit step, is discharged in
  `Analysis/ArvesonLimitStep.arvesonLimit`.  An earlier version of this bullet
  said the `B(H)` case was not there, which was true when it was written.
  `arvesonBH_of_limit` takes the isometries `Jₙ` as a parameter; for a separable
  `H` they are supplied by `Analysis/ArvesonBHSeparable`, whose
  `arvesonBH_of_separable` carries no data hypothesis at all.  This closes the
  recognition route's separable-factor specialization, but not the printed
  Theorem 4.11 with arbitrary `A` and `B`: its initial faithful representation
  can be nonseparable, so the arbitrary-H/net form of Arveson is still needed
  unless the proof is reorganized into separable reducing pieces.
* **Voiculescu's theorem is under construction, and is still one of the steps
  this module's `CompatibleTargetPairStatement` is waiting on.**  (V1) is
  `VoiculescuQuasicentral.quasicentralApproximateUnitSeparable`.  Glimm's lemma
  and the finite-dimensional intertwining assembly (V2)--(V3) are now closed,
  and `VoiculescuGlimmConsequences.separableBlockDiagonalAbsorption` closes the
  block-diagonal special case of (V4).  The general essential-representation
  recursion and the passage from mutual isometric containment to the unitary
  demanded by (V5) remain.  Once (V5) is supplied,
  `ShulmanFill.exists_calkinCompatiblePair_of_calkinUniqueness` performs the
  bundled Calkin-quotient compatibility step.  That is still not the theorem's
  final conclusion: the `(1,1)`-corner diagram must separately prove that the
  induced factor map detects the original amalgam.

The algebra `𝒟` that Theorem 10 needs is likewise no longer missing:
`Analysis/StarStrongMatrixSequencesAlgebra` builds it and its limit map, and
`Analysis/StarStrongLimitNorm` proves the direction of Theorem 4 that Theorem
10 ends with.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
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
agree on `C` precisely because Voiculescu's theorem supplied `u`.

Only `C` is required separable.  This is load-bearing: Enders--Shulman 4.11
does **not** assume `A` or `B` separable.  Their faithful representation, its
Stinespring dilations, and the infinite amplifications may therefore be
nonseparable.  The Voiculescu input they cite is the rank-matching form on that
ambient Hilbert space, not the separable-Hilbert
`ShulmanFill.CalkinUniquenessStatement` currently under construction.  Earlier
versions of this definition accidentally added `SeparableSpace A` and
`SeparableSpace B`; that strengthened the hypothesis and did not formalize the
printed theorem 1:1. -/
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

/-- The bare target-valued witness also recovers the compatible-pair form.
Restrict its map `e` to the two canonical copies of `D` in the symmetric
double.  The restrictions agree on `C`, and the universal property says that
the map induced by this recovered pair is exactly the original `e`.

Thus the two statements in the ES 4.11 interface differ only in whether the
compatible pair is exposed as data; neither is a stronger analytic input. -/
theorem compatibleTargetPair_of_calkinWitness
    (h : CalkinWitnessStatement) : CompatibleTargetPairStatement := by
  intro C A B D _ _ _ _ _ iA iB _ gamma alpha beta hA hB hC halpha hbeta
  obtain ⟨T, hTalg, hTnt, e, hinj⟩ :=
    h iA iB gamma alpha beta hA hB hC halpha hbeta
  letI : CStarAlgebra T := hTalg
  haveI : Nontrivial T := hTnt
  let sigmaA : D →⋆ₐ[ℂ] T :=
    e.comp (universalCStarAmalgamLeft gamma gamma)
  let sigmaB : D →⋆ₐ[ℂ] T :=
    e.comp (universalCStarAmalgamRight gamma gamma)
  have hsigma : sigmaA.comp gamma = sigmaB.comp gamma := by
    apply StarAlgHom.ext
    intro c
    change e (universalCStarAmalgamLeft gamma gamma (gamma c)) =
      e (universalCStarAmalgamRight gamma gamma (gamma c))
    exact congrArg e
      (DFunLike.congr_fun
        (universalCStarAmalgam_compatible gamma gamma) c)
  let R : CStarAmalgamRepresentation gamma gamma :=
    CStarAmalgamRepresentation.ofCompatiblePair
      gamma gamma sigmaA sigmaB hsigma
  let e' : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] T :=
    universalCStarAmalgamEval gamma gamma R
  have he' : e' = e := by
    obtain ⟨f, _, hunique⟩ :=
      universalCStarAmalgam_existsUnique_lift gamma gamma sigmaA sigmaB hsigma
    have he_f : e = f := hunique e ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
    have he'_f : e' = f := hunique e' ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
    exact he'_f.trans he_f.symm
  refine ⟨T, hTalg, hTnt, sigmaA, sigmaB, hsigma, ?_⟩
  change Function.Injective
    (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e')
  rw [he']
  exact hinj

/-- The two well-typed formulations of Enders--Shulman 4.11 used in this
repository are logically equivalent. -/
theorem compatibleTargetPair_iff_calkinWitness :
    CompatibleTargetPairStatement ↔ CalkinWitnessStatement :=
  ⟨calkinWitness_of_compatibleTargetPair,
    compatibleTargetPair_of_calkinWitness⟩

end

end ShulmanSymmetricDouble
end GroupApproximation
