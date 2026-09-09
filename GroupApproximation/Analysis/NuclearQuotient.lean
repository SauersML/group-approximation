import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Meta.AxiomGuard

/-!
# Nuclearity along a surjection, and the exact lifting it needs

## Why this module exists

`Manuscript/OneSidedMFRadical/MaximalCStarWNotNuclear.lean` needs one
permanence property the manuscript uses without comment: the completely
positive approximation property passes from a C⋆-algebra to its quotients.
That is the Choi--Effros theorem, and this repository does not prove it.

Rather than leave the gap as an opaque input, this module proves the half of
it that is elementary and names the half that is not.

* `isNuclearCStarAlgebra_of_cpcApproximateSection` — **a theorem.**  If
  `π : A → B` is a ⋆-homomorphism, `A` is nuclear, and `π` admits *completely
  positive contractive approximate sections* — for each finite subset of `B`
  and each tolerance, a completely positive contraction `σ : B → A` with
  `π ∘ σ` close to the identity there — then `B` is nuclear.  The proof is the
  `ε/2` composition: `α ∘ σ` goes down and `π ∘ β` comes back, and the extra
  error is the section's own.
* `CPCLocalLiftingInput` — the residual, as a named proposition: *every*
  surjective ⋆-homomorphism of C⋆-algebras admits such sections.  This is the
  lifting half of Choi--Effros and is not proved here.
* `NuclearCStarQuotientInput` — the conclusion, also as a named proposition,
  so that a downstream endpoint can carry the permanence property itself when
  that reads more honestly than carrying the lifting.

`nuclearCStarQuotientInput_of_cpcLocalLiftingInput` connects the two, so a
future lane that formalizes the lifting gets the permanence property, and with
it the manuscript's `C^*_{\max}` sentence, at no further cost.

## Why the section is where the difficulty sits

For the surjection this development cares about — the canonical map
`C^*_{\max}(G) → C^*_λ(G)` — the *obvious* candidate section is the one that
sends a finite combination of translations back to the same combination of
universal unitaries, and for a nonamenable `G` that map is not even positive.
Some self-adjoint `a = Σ_{g ∈ F} c_g λ_g` has `‖a‖_λ < ‖a‖_max`, so
`‖a‖_λ · 1 - a` is positive in the reduced algebra and not in the maximal one:
the two positive cones already differ on the operator system spanned by
finitely many translations, which is what `C^*_{\max} ≠ C^*_λ` means.

Whether *some* other completely positive contractive approximate section
exists for that map is a genuine question and is not settled here; what the
paragraph above rules out is the naive construction.  The hypothesis of
`isNuclearCStarAlgebra_of_cpcApproximateSection` is therefore not a
technicality that a clever choice of section removes — in the Choi--Effros
theorem the sections exist *because* the source is nuclear, and producing them
is the whole content.

## Manuscript status

Infrastructure.  Certifies no manuscript step on its own; it narrows one
standing input and proves the composition step around it.
-/

namespace GroupApproximation
namespace CStarExactness

universe u v

/-! ## The composition step, proved -/

/-- **Nuclearity passes along a ⋆-homomorphism with completely positive
contractive approximate sections.**

Given a finite `F ⊆ B` and a tolerance, take a section `σ` accurate to `ε/2`
on `F`, and a nuclear factorization of `A` accurate to `ε/2` on `σ(F)`.  Then
`α ∘ σ` and `π ∘ β` are completely positive contractions through the same
finite-dimensional algebra, and

`‖π(β(α(σ b))) - b‖ ≤ ‖π(β(α(σ b)) - σ b)‖ + ‖π(σ b) - b‖ ≤ ε/2 + ε/2`,

the first term because a ⋆-homomorphism of C⋆-algebras is contractive. -/
theorem isNuclearCStarAlgebra_of_cpcApproximateSection
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (π : A →⋆ₐ[ℂ] B) (hA : IsNuclearCStarAlgebra A)
    (hsec : ∀ (F : Finset B) (ε : ℝ), 0 < ε →
      ∃ σ : B →ₗ[ℂ] A, IsCompletelyPositive σ ∧ (∀ b : B, ‖σ b‖ ≤ ‖b‖) ∧
        ∀ b ∈ F, ‖π (σ b) - b‖ ≤ ε) :
    IsNuclearCStarAlgebra B := by
  classical
  intro F ε hε
  obtain ⟨sigma, hsigmaCP, hsigmaContract, hsigmaApprox⟩ :=
    hsec F (ε / 2) (div_pos hε (by norm_num))
  obtain ⟨D, alpha, beta, halpha, hbeta, halphaContract, hbetaContract,
    happrox⟩ := hA (F.image ⇑sigma) (ε / 2) (div_pos hε (by norm_num))
  refine ⟨D, alpha.comp sigma, (π : A →ₗ[ℂ] B).comp beta,
    halpha.comp hsigmaCP,
    (isCompletelyPositive_of_starAlgHom π.toNonUnitalStarAlgHom).comp hbeta,
    ?_, ?_, ?_⟩
  · intro b
    exact le_trans (halphaContract (sigma b)) (hsigmaContract b)
  · intro d
    exact le_trans (NonUnitalStarAlgHom.norm_apply_le π (beta d))
      (hbetaContract d)
  · intro b hb
    have h1 : ‖beta (alpha (sigma b)) - sigma b‖ ≤ ε / 2 :=
      happrox (sigma b) (Finset.mem_image_of_mem _ hb)
    have h2 : ‖π (sigma b) - b‖ ≤ ε / 2 := hsigmaApprox b hb
    have h3 : ‖π (beta (alpha (sigma b))) - π (sigma b)‖ ≤ ε / 2 := by
      have hmap : π (beta (alpha (sigma b))) - π (sigma b)
          = π (beta (alpha (sigma b)) - sigma b) := by
        rw [map_sub]
      rw [hmap]
      exact le_trans (NonUnitalStarAlgHom.norm_apply_le π _) h1
    show ‖π (beta (alpha (sigma b))) - b‖ ≤ ε
    calc ‖π (beta (alpha (sigma b))) - b‖
        = ‖(π (beta (alpha (sigma b))) - π (sigma b)) + (π (sigma b) - b)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖π (beta (alpha (sigma b))) - π (sigma b)‖ + ‖π (sigma b) - b‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h3 h2
      _ = ε := by ring

/-! ## The two named inputs -/

/-- **A sufficient condition for quotient permanence**, as a named
proposition: every surjective ⋆-homomorphism of C⋆-algebras admits completely
positive contractive approximate sections.

**This proposition is not known to be true, and nothing here asserts that it
is.**  It is *not* the Choi--Effros lifting theorem, which lifts completely
positive contractions whose **source** is separable and nuclear; here the
source of the section is the quotient, which is exactly the algebra whose
nuclearity is in question.  So this is a sufficient condition offered for the
sake of the implication below and for no other reason: a conditional statement
built on it would be worth nothing if it is false, which is why the manuscript
endpoints carry `NuclearCStarQuotientInput` — a genuine classical theorem —
instead.

Quantified over all C⋆-algebras and all surjections; not proved here. -/
def CPCLocalLiftingInput : Prop :=
  ∀ (A : Type u) (B : Type v) (_ : CStarAlgebra A) (_ : CStarAlgebra B)
    (π : A →⋆ₐ[ℂ] B), Function.Surjective π →
      ∀ (F : Finset B) (ε : ℝ), 0 < ε →
        ∃ σ : B →ₗ[ℂ] A, IsCompletelyPositive σ ∧ (∀ b : B, ‖σ b‖ ≤ ‖b‖) ∧
          ∀ b ∈ F, ‖π (σ b) - b‖ ≤ ε

/-- **Nuclearity passes to quotients**, as a named proposition: the
Choi--Effros permanence property, quantified over all C⋆-algebras and all
surjections.  Not proved here. -/
def NuclearCStarQuotientInput : Prop :=
  ∀ (A : Type u) (B : Type v) (_ : CStarAlgebra A) (_ : CStarAlgebra B)
    (π : A →⋆ₐ[ℂ] B), Function.Surjective π →
      IsNuclearCStarAlgebra A → IsNuclearCStarAlgebra B

/-- **The lifting gives the permanence property.**  With the sections in hand,
the composition step above does the rest, so a lane that formalizes
Choi--Effros lifting closes the quotient row with no further work. -/
theorem nuclearCStarQuotientInput_of_cpcLocalLiftingInput
    (lifting : CPCLocalLiftingInput.{u, v}) :
    NuclearCStarQuotientInput.{u, v} := by
  intro A B instA instB π hπ hA
  exact isNuclearCStarAlgebra_of_cpcApproximateSection π hA
    (fun F ε hε ↦ lifting A B instA instB π hπ F ε hε)

end CStarExactness
end GroupApproximation

open GroupApproximation.CStarExactness

#audit_axioms
  GroupApproximation.CStarExactness.isNuclearCStarAlgebra_of_cpcApproximateSection

#audit_axioms
  GroupApproximation.CStarExactness.nuclearCStarQuotientInput_of_cpcLocalLiftingInput
