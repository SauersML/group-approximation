import GroupApproximation.Analysis.CuntzPedersenCoronaObstruction

/-!
# Pulling a singular quotient trace back to a uniform tracial completion

This file formalizes the last quotient step in the negative solution to
Problem XXII.  The statement deliberately separates the three maps involved:

* `ι : A → M`, the inclusion into the uniform tracial completion;
* `π : M → H`, the quotient by the original `c₀` ideal; and
* `τ∞`, the scalar quotient trace on `A`.

If `π (ι a) = τ∞(a) 1`, every tracial state of `H` pulls back to an extension
of `τ∞`.  A quotient trace detecting `π h` is therefore different from the
uniform-`2`-continuous extension, which kills `h`.  This is exactly the final
calculation in the proposed counterexample and contains no continuity or
surjectivity assumption hidden in notation.
-/

namespace GroupApproximation
namespace UniformTracialCompletionTraceExtension

noncomputable section

universe u v w

variable {A : Type u} {M : Type v} {H : Type w}
  [CStarAlgebra A] [CStarAlgebra M] [CStarAlgebra H]

/-- A trace on the norm quotient which detects the `2`-null class pulls back
to a genuinely different extension of the scalar quotient trace. -/
theorem exists_rogue_extension
    (ι : A →⋆ₐ[ℂ] M) (π : M →⋆ₐ[ℂ] H)
    (tauInf : TracialState A) (τu : TracialState M) (σ : TracialState H)
    (h : M)
    (hscalar : ∀ a : A, π (ι a) = algebraMap ℂ H (tauInf a))
    (huniform : ∀ a : A, τu (ι a) = tauInf a)
    (hτu : τu h = 0) (hσ : σ (π h) ≠ 0) :
    ∃ σM : TracialState M,
      (∀ a : A, σM (ι a) = tauInf a) ∧
      (∀ a : A, σM (ι a) = τu (ι a)) ∧
      σM h ≠ τu h := by
  let σM : TracialState M := σ.compStarAlgHom π
  refine ⟨σM, fun a ↦ ?_, fun a ↦ ?_, ?_⟩
  · rw [TracialState.compStarAlgHom_apply, hscalar,
      CuntzPedersenCoronaObstruction.tracialState_map_algebraMap]
  · calc
      σM (ι a) = tauInf a := by
        rw [TracialState.compStarAlgHom_apply, hscalar,
          CuntzPedersenCoronaObstruction.tracialState_map_algebraMap]
      _ = τu (ι a) := (huniform a).symm
  · rw [TracialState.compStarAlgHom_apply, hτu]
    exact hσ

/-- Consequently restriction of traces along `ι` is not injective.  This is
the set-theoretic strictness assertion behind
`T(A) ⊊ T(overline A^{T(A)})`, stated without identifying trace spaces with a
particular bundled simplex type. -/
theorem trace_restriction_not_injective
    (ι : A →⋆ₐ[ℂ] M) (π : M →⋆ₐ[ℂ] H)
    (tauInf : TracialState A) (τu : TracialState M) (σ : TracialState H)
    (h : M)
    (hscalar : ∀ a : A, π (ι a) = algebraMap ℂ H (tauInf a))
    (huniform : ∀ a : A, τu (ι a) = tauInf a)
    (hτu : τu h = 0) (hσ : σ (π h) ≠ 0) :
    ∃ σM : TracialState M,
      (∀ a : A, σM (ι a) = τu (ι a)) ∧ σM ≠ τu := by
  obtain ⟨σM, -, hagree, hne⟩ :=
    exists_rogue_extension ι π tauInf τu σ h hscalar huniform hτu hσ
  refine ⟨σM, hagree, ?_⟩
  intro heq
  exact hne (congrArg (fun ρ : TracialState M ↦ ρ h) heq)

end

end UniformTracialCompletionTraceExtension
end GroupApproximation
