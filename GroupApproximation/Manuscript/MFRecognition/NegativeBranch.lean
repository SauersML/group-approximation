import GroupApproximation.Manuscript.MFRecognition.RecognitionInputs
import GroupApproximation.Manuscript.OneSidedMFRadical.ComputabilityConstructionClosure

/-!
# `lem:negative-branch`: the case `e ∈ FIN`

> **Lemma (the case `e ∈ FIN`).**  If `e ∈ FIN`, then `H` embeds in `R̂_e`,
> and `R̂_e` is not MF.
>
> *Proof.*  For `e ∈ FIN` we have
> `H ≤ C_e ≤ Q_e ≤ Γ_e × Q_e ≤ R_e ≅ R̂_e` by Lemmas `lem:switch`,
> `lem:bridge`(1), and `lem:finite-rope`, and Britton's lemma for
> `eq:twisted-rope`.  Restricting MF models to a subgroup shows that subgroups
> of MF groups are MF, and `H` is not MF by `[NonMF, Theorem B]`.

Each link of the printed chain is one theorem below:

| link | theorem | source |
| --- | --- | --- |
| `H ≤ C_e` | `embed_H_C` | `lem:switch` (a field of `RecognitionInputs`) |
| `C_e ≤ Q_e` | `embed_C_Q` | `lem:bridge`(1) (a field) |
| `Q_e ≤ Γ_e × Q_e` | `inr_injective` | the second-factor inclusion |
| `Γ_e × Q_e ≤ R_e` | `twistedHNN_of_injective` | Britton's lemma |
| `R_e ≅ R̂_e` | `equiv_Rhat` | `lem:finite-rope` (a field) |

The last sentence is
`ComputabilityConstruction.manuscriptPrintedNonMFEmbeddingObstruction`,
already closed in the repository: a countable group containing a countable
non-MF group cannot be MF.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Recognition

open GroupApproximation.Manuscript.OneSidedMFRadical.ComputabilityConstruction
open GroupApproximation.SecondLevelIndexSets

variable {e : Nat.Partrec.Code}
variable {H C F P Qplus Q K0 Rhat : Type}
variable [Group H] [Group C] [Group F] [Group P] [Group Qplus] [Group Q]
variable [Group K0] [Group Rhat]

/-- Composition of injective homomorphisms is injective. -/
theorem injective_comp {A B C' : Type} [Group A] [Group B] [Group C']
    {g : B →* C'} {f : A →* B} (hg : Function.Injective g)
    (hf : Function.Injective f) : Function.Injective (g.comp f) := by
  intro x y hxy
  exact hf (hg hxy)

/-- "`Q_e ≤ Γ_e × Q_e`": the second-factor inclusion of a direct product is
injective. -/
theorem inr_injective (A B : Type) [Group A] [Group B] :
    Function.Injective (MonoidHom.inr A B) := by
  intro x y hxy
  exact congrArg Prod.snd hxy

/-- The printed chain `Q_e ≤ Γ_e × Q_e ≤ R_e ≅ R̂_e`, assembled. -/
theorem embed_Q_Rhat (D : RecognitionInputs e H C F P Qplus Q K0 Rhat) :
    ∃ f : Q →* Rhat, Function.Injective f := by
  have hequiv : Function.Injective D.equiv_Rhat.toMonoidHom := by
    exact D.equiv_Rhat.injective
  have hbritton :
      Function.Injective
        (HNNExtension.of :
          (CentralRope D.L0 (D.j.comp D.qplus)) × Q →*
            TwistedHNN
              (ropeSubgroup D.L0 (D.j.comp D.qplus) D.i0) D.alpha) :=
    twistedHNN_of_injective (ropeSubgroup D.L0 (D.j.comp D.qplus) D.i0) D.alpha
  exact ⟨D.equiv_Rhat.toMonoidHom.comp
      ((HNNExtension.of :
          (CentralRope D.L0 (D.j.comp D.qplus)) × Q →*
            TwistedHNN
              (ropeSubgroup D.L0 (D.j.comp D.qplus) D.i0) D.alpha).comp
        (MonoidHom.inr (CentralRope D.L0 (D.j.comp D.qplus)) Q)),
    injective_comp hequiv (injective_comp hbritton (inr_injective _ _))⟩

/-- **The first half of `lem:negative-branch`.**  "If `e ∈ FIN`, then `H`
embeds in `R̂_e`", by the printed chain
`H ≤ C_e ≤ Q_e ≤ Γ_e × Q_e ≤ R_e ≅ R̂_e`. -/
theorem embed_H_Rhat (D : RecognitionInputs e H C F P Qplus Q K0 Rhat)
    (hFIN : FiniteDomain e) : ∃ f : H →* Rhat, Function.Injective f := by
  obtain ⟨a, ha⟩ := D.embed_H_C hFIN
  obtain ⟨b, hb⟩ := D.embed_C_Q
  obtain ⟨c, hc⟩ := embed_Q_Rhat D
  exact ⟨c.comp (b.comp a), injective_comp hc (injective_comp hb ha)⟩

/-- **The second half of `lem:negative-branch`.**  "Restricting MF models to a
subgroup shows that subgroups of MF groups are MF, and `H` is not MF by
`[NonMF, Theorem B]`." -/
theorem not_isOperatorMF_Rhat
    (D : RecognitionInputs e H C F P Qplus Q K0 Rhat)
    (hFIN : FiniteDomain e) : ¬ IsOperatorMF Rhat := by
  obtain ⟨f, hf⟩ := embed_H_Rhat D hFIN
  letI : Countable H := D.countable_H
  letI : Countable Rhat := D.countable_Rhat
  exact manuscriptPrintedNonMFEmbeddingObstruction H Rhat
    D.not_isOperatorMF_H f hf

/-- **`lem:negative-branch`, exactly as printed.**

"If `e ∈ FIN`, then `H` embeds in `R̂_e`, and `R̂_e` is not MF." -/
theorem manuscriptNegativeBranch
    (D : RecognitionInputs e H C F P Qplus Q K0 Rhat)
    (hFIN : FiniteDomain e) :
    (∃ f : H →* Rhat, Function.Injective f) ∧ ¬ IsOperatorMF Rhat :=
  ⟨embed_H_Rhat D hFIN, not_isOperatorMF_Rhat D hFIN⟩

end Recognition
end MFRecognition
end Manuscript
end GroupApproximation
