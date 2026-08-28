import GroupApproximation.Analysis.MFAlgebraAmalgamFactorMapProperties
import GroupApproximation.Analysis.ShulmanSymmetricDoubleRoute

/-!
# Theorem 13, reduced to one Calkin-algebra witness

LITERATURE INPUT: D. Enders and T. Shulman, *On the (Local) Lifting Property*,
arXiv:2403.12224, Theorem 4.11 — cited as Theorem 13 of T. Shulman, *The MF
property for amalgamated free products*, arXiv:2603.13564v2.

> Let `A`, `B`, `D` be unital `C*`-algebras and `C` separable unital.  Let
> `θ_A : C → A`, `θ_B : C → B`, `φ_A : A → D`, `φ_B : B → D` be unital
> inclusions with `φ_A ∘ θ_A = φ_B ∘ θ_B`.  Then `A *_C B` embeds into
> `D *_C D`.

## Their proof, and the one place it is analytic

Write `Φ = φ_A * φ_B : A *_C B → D *_C D` — in this repository
`symmetricDoubleEmbedding`, the peer lane's `factorAmalgamToSymmetricTarget`
taken at `e = id`.  Enders and Shulman prove `Φ` injective as follows.

1. Choose an embedding `α : A *_C B → B(H)` whose composition with the Calkin
   quotient `q : B(H) → Q(H)` is still injective; `α := j^{⊕∞}` for any
   embedding `j` does it, since an infinite amplification is faithful modulo
   the compacts.
2. `φ_A` is injective, so `α ∘ ι_A` transported to `φ_A(A) ⊆ D` is a ccp map
   there; the **Arveson extension theorem** extends it to a ccp map on `D`,
   and the **Stinespring dilation theorem** dilates that to a
   `*`-homomorphism `σ_A`.  Likewise `σ_B`.
3. **Voiculescu's theorem**, applied to
   `(σ_A φ_A ι_A)_{22} ⊕ (σ_A φ_A ι_A)^{⊕∞}` and
   `(σ_B φ_B ι_B)_{22} ⊕ (σ_B φ_B ι_B)^{⊕∞}`, produces a unitary
   `u ∈ B(H^{⊕∞})` conjugating one to the other modulo `K(H)`.
4. So `γ := (q ∘ Ad(1 ⊕ u) ∘ σ_A^{⊕∞}) * (q ∘ σ_B^{⊕∞}) : D *_C D → Q(H^{⊕∞})`
   is a well-defined `*`-homomorphism, and the diagram it sits in commutes
   through the `(·)₁₁` corner: `γ ∘ Φ` is, up to that corner, `q ∘ α`.
5. "Since `q ∘ α` is injective, so must be `φ_A * φ_B`."

Step 5 is the only step that touches `Φ`, and it is formal: a `*`-homomorphism
whose composite with something is injective is injective.  Steps 1–4 are
analytic and none of Arveson, Stinespring or Voiculescu is available here.

## What this module does

It performs step 5 and names steps 1–4 as one existence statement.

* `symmetricDoubleEmbedding` is `Φ`;
* `factorAmalgamToSymmetricTarget_eq_comp` says the peer's map at a general
  `e` is `e ∘ Φ`, by the uniqueness half of the amalgam's universal property;
* `injective_symmetricDoubleEmbedding_of_witness` is step 5;
* `CalkinWitnessStatement` is steps 1–4: some `*`-homomorphism out of the
  symmetric double composes with `Φ` to an injective map;
* `amalgamEmbedsSymmetricDouble_of_calkinWitness` turns that into
  `AmalgamEmbedsSymmetricDoubleStatement`, the form the route consumes.

The witness statement is deliberately weaker than what the paper builds: it
does not mention the Calkin algebra, amplifications or corners, only that
*some* target detects `Φ`.  Anything that produces a faithful compatible pair
for `(D, D)` extending the given one discharges it.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace ShulmanSymmetricDouble

open MFAlgebraAmalgamCriterion

noncomputable section

variable {C A B D : Type}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra D] [Nontrivial D]
  (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
  [Nonempty (CStarAmalgamRepresentation iA iB)]
  (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
  (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)

/-! ## The symmetric double is nontrivial -/

/-- The left factor of a symmetric double is faithful: the identity pair is a
compatible coordinate. -/
theorem universalCStarAmalgamLeft_symmetric_injective :
    Function.Injective (universalCStarAmalgamLeft gamma gamma) :=
  universalCStarAmalgamLeft_injective_of_coordinate gamma gamma
    (symmetricIdentityRepresentation gamma) fun _ _ h ↦ h

/-- A symmetric double of a nontrivial algebra is nontrivial, so it may be
used as the target `E` of the peer lane's factor map. -/
instance nontrivial_universalCStarSymmetricAmalgam :
    Nontrivial (UniversalCStarAmalgam gamma gamma) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne D
  exact ⟨⟨universalCStarAmalgamLeft gamma gamma x,
    universalCStarAmalgamLeft gamma gamma y,
    fun h ↦ hxy (universalCStarAmalgamLeft_symmetric_injective gamma h)⟩⟩

/-! ## `Φ = φ_A * φ_B`, and the factorization of the peer's map through it -/

/-- **The map of Theorem 13.**  `Φ : A *_C B → D *_C D`, sending the left
factor through `alpha` into the first copy of `D` and the right factor through
`beta` into the second. -/
def symmetricDoubleEmbedding :
    UniversalCStarAmalgam iA iB →⋆ₐ[ℂ] UniversalCStarAmalgam gamma gamma :=
  factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB
    (StarAlgHom.id ℂ (UniversalCStarAmalgam gamma gamma))

@[simp] theorem symmetricDoubleEmbedding_left (a : A) :
    symmetricDoubleEmbedding iA iB gamma alpha beta hA hB
        (universalCStarAmalgamLeft iA iB a) =
      universalCStarAmalgamLeft gamma gamma (alpha a) := rfl

@[simp] theorem symmetricDoubleEmbedding_right (b : B) :
    symmetricDoubleEmbedding iA iB gamma alpha beta hA hB
        (universalCStarAmalgamRight iA iB b) =
      universalCStarAmalgamRight gamma gamma (beta b) := rfl

/-- The peer lane's factor map at a general target is `e ∘ Φ`.  Both sides are
`*`-homomorphisms out of the amalgam agreeing on the two factor images, so the
uniqueness half of `universalCStarAmalgam_existsUnique_lift` identifies
them. -/
theorem factorAmalgamToSymmetricTarget_eq_comp
    {E : Type} [CStarAlgebra E] [Nontrivial E]
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) :
    factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e =
      e.comp (symmetricDoubleEmbedding iA iB gamma alpha beta hA hB) := by
  have hcompat :
      (e.comp ((universalCStarAmalgamLeft gamma gamma).comp alpha)).comp iA =
        (e.comp ((universalCStarAmalgamRight gamma gamma).comp beta)).comp iB := by
    apply StarAlgHom.ext
    intro c
    change e (universalCStarAmalgamLeft gamma gamma (alpha (iA c))) =
      e (universalCStarAmalgamRight gamma gamma (beta (iB c)))
    rw [DFunLike.congr_fun hA c, DFunLike.congr_fun hB c]
    exact congrArg e
      (DFunLike.congr_fun (universalCStarAmalgam_compatible gamma gamma) c)
  obtain ⟨_, _, huniq⟩ :=
    universalCStarAmalgam_existsUnique_lift iA iB
      (e.comp ((universalCStarAmalgamLeft gamma gamma).comp alpha))
      (e.comp ((universalCStarAmalgamRight gamma gamma).comp beta)) hcompat
  exact (huniq _ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩).trans
    (huniq _ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩).symm

/-! ## Step 5, and the witness that steps 1–4 supply -/

/-- **Step 5 of Enders--Shulman, Theorem 4.11.**  If some target detects the
amalgam through the symmetric double, then `Φ` is injective. -/
theorem injective_symmetricDoubleEmbedding_of_witness
    {E : Type} [CStarAlgebra E] [Nontrivial E]
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E)
    (he : Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e)) :
    Function.Injective
      (symmetricDoubleEmbedding iA iB gamma alpha beta hA hB) := by
  rw [factorAmalgamToSymmetricTarget_eq_comp] at he
  intro x y hxy
  exact he (congrArg e hxy)

/-- **Steps 1–4 of Enders--Shulman, Theorem 4.11**, as one existence
statement: the Calkin-algebra construction, with everything about the Calkin
algebra forgotten except its conclusion. -/
def CalkinWitnessStatement : Prop :=
  ∀ {C A B D : Type} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra D] [Nontrivial D]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma),
      TopologicalSpace.SeparableSpace C →
      Function.Injective alpha → Function.Injective beta →
        ∃ E : Type, ∃ _ : CStarAlgebra E, ∃ _ : Nontrivial E,
          ∃ e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E,
            Function.Injective
              (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e)

/-- **Theorem 13 from the Calkin witness.**  Everything except the witness is
proved. -/
theorem amalgamEmbedsSymmetricDouble_of_calkinWitness
    (hwitness : CalkinWitnessStatement) :
    AmalgamEmbedsSymmetricDoubleStatement := by
  intro C A₁ A₂ D _ _ _ _ iA iB k phiA phiB _ _ hC hphiA hphiB hkA hkB
  haveI : Nontrivial D := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne A₁
    exact ⟨⟨phiA x, phiA y, fun h ↦ hxy (hphiA h)⟩⟩
  have hA : phiA.comp iA = k := by
    apply StarAlgHom.ext
    intro c
    exact hkA c
  have hB : phiB.comp iB = k := by
    apply StarAlgHom.ext
    intro c
    exact hkB c
  obtain ⟨E, hEalg, hEnt, e, he⟩ :=
    hwitness iA iB k phiA phiB hA hB hC hphiA hphiB
  letI : CStarAlgebra E := hEalg
  haveI : Nontrivial E := hEnt
  exact ⟨symmetricDoubleEmbedding iA iB k phiA phiB hA hB,
    injective_symmetricDoubleEmbedding_of_witness iA iB k phiA phiB hA hB e he⟩

end

end ShulmanSymmetricDouble
end GroupApproximation
