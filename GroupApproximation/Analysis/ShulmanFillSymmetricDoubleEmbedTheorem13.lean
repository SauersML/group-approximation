import GroupApproximation.Analysis.MFAlgebraAmalgamFactorMapProperties
import GroupApproximation.Analysis.ShulmanSymmetricDoubleRoute

/-!
# Theorem 13: its Calkin witness, and the universe obstruction to `Φ`

LITERATURE INPUT: D. Enders and T. Shulman, *On the (Local) Lifting Property*,
arXiv:2403.12224, Theorem 4.11 — cited as Theorem 13 of T. Shulman, *The MF
property for amalgamated free products*, arXiv:2603.13564v2.

> Let `A`, `B`, `D` be unital `C*`-algebras and `C` separable unital.  Let
> `θ_A : C → A`, `θ_B : C → B`, `φ_A : A → D`, `φ_B : B → D` be unital
> inclusions with `φ_A ∘ θ_A = φ_B ∘ θ_B`.  Then `A *_C B` embeds into
> `D *_C D`.

## Their proof, and the one place it is analytic

Write `Φ = φ_A * φ_B : A *_C B → D *_C D`.  Enders and Shulman prove `Φ`
injective as follows.  (`Φ` is not a term of this repository; see the universe
obstruction below.)

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

## The universe obstruction: `Φ` cannot be typed

Step 5 above is formal, but `Φ` itself does not exist as a term of this
repository's amalgam.  `MFAlgebraAmalgamCriterion.factorAmalgamToSymmetricTarget`
is `universalCStarAmalgamEval` at a `CStarAmalgamRepresentation`, whose
`carrier` lies in the same universe as `C`, `A`, `B` — so its target is fixed in
`Type`.  `UniversalCStarAmalgam gamma gamma` lies one universe *up*, being a
subalgebra of a product indexed by a `Type`-valued structure.  Taking `e = id`
therefore does not typecheck, and universe-polymorphising the carrier cannot
help: it would need `v = max (u + 1) (v + 1)`.

So `symmetricDoubleEmbedding`, `symmetricDoubleEmbedding_left`/`_right`,
`factorAmalgamToSymmetricTarget_eq_comp`,
`injective_symmetricDoubleEmbedding_of_witness` and
`amalgamEmbedsSymmetricDouble_of_calkinWitness` have been **deleted**: they were
ill-typed, not merely unproved.  Nothing outside this module and
`Analysis/ShulmanFillTheorem13` used them.

## What this module does now

It names steps 1–4 and nothing else.

* `universalCStarAmalgamLeft_symmetric_injective` and
  `nontrivial_universalCStarSymmetricAmalgam` are unaffected and kept;
* `CalkinWitnessStatement` is steps 1–4, and is well-typed as written: its
  target `E` is already in `Type`.

## The repaired reduction, and why the witness is not enough

`Analysis/ShulmanFillNormingAmalgamWitness` carries the repair.  The consumer
never wanted `Φ`: `isMFAlgebra_of_injective_into_symmetricDouble` immediately
composed it with the corona embedding that MF-ness of the double supplies, and
*that composite* is `factorAmalgamToSymmetricTarget` at a `Type`-valued target,
which is well-typed.  The operative hypothesis is therefore

> for every `Type`-valued `E` and every faithful
> `g : D *_C D →⋆ₐ[ℂ] E`, the map
> `factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB g` is faithful,

which is exactly "`Φ` is injective" said without naming `Φ`, and is what
Enders--Shulman's argument delivers.

`CalkinWitnessStatement` below is *not* sufficient for that conclusion, and is
kept only as the record of steps 1–4.  It provides one target `E`, chosen by
whoever discharges it, and MF-ness of the amalgam needs the target to be
MF-embeddable; in the paper `E = Q(H^{⊕∞})` is the Calkin algebra, which is not
even stably finite.  The `∀`-form above is what the route consumes.

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

/-! ## The witness that steps 1–4 supply -/

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

end

end ShulmanSymmetricDouble
end GroupApproximation
