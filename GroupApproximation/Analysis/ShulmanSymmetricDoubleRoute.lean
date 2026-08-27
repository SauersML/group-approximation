import GroupApproximation.Analysis.MFAlgebraAmalgamGenerated
import GroupApproximation.Analysis.ShulmanFillTheorem16

/-!
# Shulman's own route to Theorem 16: the symmetric double

LITERATURE INPUT: T. Shulman, *The MF property for amalgamated free products*,
arXiv:2603.13564v2 (submitted 13 March 2026, revised 22 March 2026), Theorem
16, with Theorems 10 and 13 and Lemmas 7, 8, 9 and 15 of the same paper.  The
statements below are the paper's; nothing here is proved from them that the
paper does not prove.

## What the paper actually does

Theorem 16 there is an *equivalence*: for separable `A`, `B`, `C` with
inclusions `θ_A : C → A` and `θ_B : C → B`, the full amalgam `A *_C B` is MF
if and only if there are embeddings `φ_A : A → ∏Mₙ/⊕Mₙ` and
`φ_B : B → ∏Mₙ/⊕Mₙ` with `φ_A ∘ θ_A = φ_B ∘ θ_B`.  The printed criterion of
`HNNPermanenceCitations.ShulmanTheorem16Statement` is its "if" half.

The proof of that half is three steps and no estimate:

1. put `D = C*(φ_A(A), φ_B(B))`, a separable subalgebra of the corona, so `D`
   is MF;
2. **Theorem 13**: unital embeddings of `A` and `B` into one `D` agreeing on
   `C` make `A *_C B` embed into the *symmetric double* `D *_C D`;
3. **Theorem 10**: `D *_C D` is MF for every separable MF `D` and every
   subalgebra `C ⊆ D`.

The non-unital case is forced unitization plus Lemma 15,
`A⁺ *_{C⁺} B⁺ = (A *_C B)⁺`.

## Why the double is what makes the argument elementary

Theorem 10 is proved by symmetry, not by a genericity estimate.  Given a
faithful `π = π₁ * π₂ : A *_C A → B(H)`, set `ρ₁ = π₁ ⊕ π₂` and
`ρ₂ = π₂ ⊕ π₁`.  Because the two factors of a *double* are copies of the same
algebra, the flip `u = ((0,1),(1,0))` conjugates one into the other,
`ρ₁ = u* ρ₂ u`, and — this is the point — `ρ₁` and `ρ₂` *agree on* `C`, so
`u` commutes with `ρ₂(C)` exactly.  Lemma 9 (a Halmos dilation of a
quasicentrally corrected contractive lift) then lifts `u ⊕ -u*` to unitaries
`V_k ∈ M₄(𝒟)` with `‖[V_k, φ_k(c) ⊕ φ_k(c)]‖ ≤ 1/k` on the `k`-th initial
segment of a dense sequence of `C`.  With `φ⁽²⁾_k = φ_k ⊕ φ_k` and
`φ⁽¹⁾_k = V_k* φ⁽²⁾_k V_k`, the two asymptotic homomorphisms agree
asymptotically on `C`, so Lemma 7 glues them into one asymptotic homomorphism
on `A *_C A` lifting `(ρ₁⊕ρ₁) * (ρ₂⊕ρ₂)`, and Theorem 4 concludes.

So the unitary that decouples the two factors is produced by an *exact*
commutation relation coming from the symmetry of the double, and only its
*lift* is approximate.  No Haagerup--Thorbjørnsen genericity estimate enters.

## Relation to the norming route in this repository

`Analysis/ShulmanFillTheorem16`, `Analysis/ShulmanFillDenseNorming` and
`Analysis/ShulmanFillWordNorming` reduce Theorem 16 to
`ShulmanFill.WordNormingStatement`, and `Analysis/ShulmanFillConjugatePair`
reduces that further to a conjugated form whose step 5 — the conjugated pair
reproducing the full amalgam norm on a word — its own docstring calls "of
Haagerup--Thorbjørnsen type and not in the repository".  That step is a
genuine gap, and it is not a step of Shulman's proof: his Theorem 10 replaces
it by the symmetry above.  The norming reduction is sound, but the route
below is the one the citation supports.

## What the repository already has for this route

Step 1 is done: `MFAlgebraAmalgamGenerated.compatibleGeneratedSubalgebra` is
`D`, `compatibleGenerated_isMFAlgebra` proves it MF, and
`compatibleGenerated_comp_eq` and `compatibleGenerated_factor_injective` give
the compatible faithful corestrictions.  Steps 2 and 3 are the two statements
named below.  This module proves the passage from them to the MF property of
the amalgam; instantiating `D` and handling the non-unital case are the
remaining glue, and neither is an estimate.

This module is not in the root import list.  It was authored while builds were
suspended, so it is kept out of the closure until it has been elaborated.
-/

namespace GroupApproximation
namespace ShulmanSymmetricDouble

noncomputable section

/-- **Shulman, Theorem 10.**  The symmetric double of a separable MF algebra
over any subalgebra is MF.  This is the analytic core of the paper's proof of
Theorem 16, and the only one of its steps that is not formal. -/
def SymmetricDoubleMFStatement : Prop :=
  ∀ {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
    (k : C →⋆ₐ[ℂ] D) [Nonempty (CStarAmalgamRepresentation k k)],
      IsMFAlgebra D → IsMFAlgebra (UniversalCStarAmalgam k k)

/-- **Shulman, Theorem 13.**  Two faithful unital maps into one algebra `D`
that agree on `C` make the amalgam embed into the symmetric double of `D`.
The paper attributes this to its reference [9]; it is a statement about
amalgamated free products alone, with no approximation in it. -/
def AmalgamEmbedsSymmetricDoubleStatement : Prop :=
  ∀ {C A₁ A₂ D : Type} [CStarAlgebra C] [CStarAlgebra A₁]
    [CStarAlgebra A₂] [CStarAlgebra D]
    (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂) (k : C →⋆ₐ[ℂ] D)
    (phiA : A₁ →⋆ₐ[ℂ] D) (phiB : A₂ →⋆ₐ[ℂ] D)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    [Nonempty (CStarAmalgamRepresentation k k)],
      TopologicalSpace.SeparableSpace C →
      Function.Injective phiA → Function.Injective phiB →
        (∀ c : C, phiA (iA c) = k c) → (∀ c : C, phiB (iB c) = k c) →
          ∃ e : UniversalCStarAmalgam iA iB →⋆ₐ[ℂ] UniversalCStarAmalgam k k,
            Function.Injective e

/-- An amalgam that embeds in an MF symmetric double is itself MF.  MF
embeddability passes backward along a faithful star homomorphism, and so does
separability, so nothing about the amalgam has to be checked separately. -/
theorem isMFAlgebra_of_injective_into_symmetricDouble
    {C A₁ A₂ D : Type} [CStarAlgebra C] [CStarAlgebra A₁] [CStarAlgebra A₂]
    [CStarAlgebra D] {iA : C →⋆ₐ[ℂ] A₁} {iB : C →⋆ₐ[ℂ] A₂} {k : C →⋆ₐ[ℂ] D}
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    [Nonempty (CStarAmalgamRepresentation k k)]
    (hdouble : IsMFAlgebra (UniversalCStarAmalgam k k))
    (e : UniversalCStarAmalgam iA iB →⋆ₐ[ℂ] UniversalCStarAmalgam k k)
    (he : Function.Injective e) :
    IsMFAlgebra (UniversalCStarAmalgam iA iB) :=
  hdouble.of_injective_nonUnitalStarAlgHom e.toNonUnitalStarAlgHom he

/-- **Steps 2 and 3 of Shulman's proof, composed.**  At a fixed `D` carrying
faithful maps of both factors that agree on `C`, Theorems 13 and 10 make the
amalgam MF.  What is left of Theorem 16 after this is the choice of `D` —
`MFAlgebraAmalgamGenerated.compatibleGeneratedSubalgebra`, already proved MF —
and the passage from the printed non-unital corona embeddings to unital ones,
which is Shulman's Lemma 15 and, in this repository,
`Analysis/CompatibleCoronaSupportCorner`. -/
theorem isMFAlgebra_amalgam_of_symmetricDoubleRoute
    (hDouble : SymmetricDoubleMFStatement)
    (hEmbed : AmalgamEmbedsSymmetricDoubleStatement)
    {C A₁ A₂ D : Type} [CStarAlgebra C] [CStarAlgebra A₁] [CStarAlgebra A₂]
    [CStarAlgebra D] (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂) (k : C →⋆ₐ[ℂ] D)
    (phiA : A₁ →⋆ₐ[ℂ] D) (phiB : A₂ →⋆ₐ[ℂ] D)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    [Nonempty (CStarAmalgamRepresentation k k)]
    (hC : TopologicalSpace.SeparableSpace C)
    (hD : IsMFAlgebra D)
    (hphiA : Function.Injective phiA) (hphiB : Function.Injective phiB)
    (hkA : ∀ c : C, phiA (iA c) = k c) (hkB : ∀ c : C, phiB (iB c) = k c) :
    IsMFAlgebra (UniversalCStarAmalgam iA iB) := by
  obtain ⟨e, he⟩ := hEmbed iA iB k phiA phiB hC hphiA hphiB hkA hkB
  exact isMFAlgebra_of_injective_into_symmetricDouble (hDouble k hD) e he

end

end ShulmanSymmetricDouble
end GroupApproximation
