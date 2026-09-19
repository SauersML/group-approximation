import GroupApproximation.Analysis.ShulmanFillNormingTheorem4Refuted

/-!
# Theorem 4's lifting direction with the model chosen after the representation

`Analysis/ShulmanFillNormingTheorem4Refuted` refutes the form of Shulman's
Theorem 4 that this repository first recorded, in which the matricial model is
quantified *before* the representation: `not_theorem4ModelFirst` shows that
`Theorem4ModelFirstStatement` forces every separable MF algebra with a faithful
representation to be commutative, because the scalar model `A n = ℂ`,
`ι n z = z • 1` makes `𝒟` commutative while the `lift` clause is exact.

The fault is the quantifier order, and the repair is to put the model *after*
the representation, which is what Blackadar--Kirchberg actually supply: the
matricial field is built to fit `π`.  `Theorem4RepresentationFirstStatement`
below is that form.  It is the honest binder for the lifting direction, and it
is what the headers of `Analysis/ShulmanFillNormingDoubleMF` and
`Analysis/ShulmanFillNormingConjugationLift` describe in prose.

## The scalar-model refutation does not touch this form

Under the model-first statement the algebra `𝒟` is fixed before `π` is chosen,
so `range q` is fixed too, and the scalar model exhibits a `𝒟` in which no
noncommutative algebra can be lifted.  Here `A`, `ι`, `hnorm` and `hone` are
produced from `π`, so no single `𝒟` is asked to receive every representation
and the argument of `commute_of_theorem4ModelFirst` has nothing to bite on.

What is recorded below in Lean is the weakening itself:
`theorem4RepresentationFirst_of_modelFirst` derives the representation-first
form from the model-first one by choosing the scalar model.  Since the
model-first form is false, that implication carries no evidence *for* the new
statement; its content is the comparison — the repair only ever asks for less,
so nothing that was provable before this module has been strengthened.

## Instances inside the existential

`A n` has to carry a C-star algebra structure before `ι n : A n →⋆ₙₐ[ℂ] B(H)`
can even be stated, so the structure is bound by the existential and re-declared
with `letI` before the binders that use it.  This is the idiom of
`MFAlgebraUnitalCoronaEmbedding.exists_injective_unital_coronaEmbedding`, and it
keeps the statement elaborating without any `@`-applications.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-- **Shulman's Theorem 4, lifting direction, with the model after the
representation.**  For every separable Hilbert space `H`, every separable MF
algebra `B` and every faithful representation `π : B →⋆ₐ[ℂ] B(H)` there is a
family of C-star algebras `A n` with MF coefficients, a contractive family of
embeddings `ι n : A n → B(H)` whose units converge strongly to `1`, and a
discrete asymptotic homomorphism of `B` into the resulting `𝒟` lifting `π`
through the `*`-strong limit map.

The model-first form of this, in which `A`, `ι`, `hnorm` and `hone` are
quantified before `B` and `π`, is `Theorem4ModelFirstStatement` and is refuted
by `not_theorem4ModelFirst`. -/
def Theorem4RepresentationFirstStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (B : Type) [CStarAlgebra B] [TopologicalSpace.SeparableSpace B],
      IsMFAlgebra B →
      ∀ π : B →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective π →
        ∃ (A : ℕ → Type) (hcstar : ∀ n, CStarAlgebra (A n)),
          letI : ∀ n, CStarAlgebra (A n) := hcstar
          ∃ hnontrivial : ∀ n, Nontrivial (A n),
            letI : ∀ n, Nontrivial (A n) := hnontrivial
            ∃ (_ : ∀ n, HasMFEmbedding (A n))
              (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
              (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
              (hone : ∀ v : H,
                Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)),
              Nonempty (StarStrongAsymptoticLift ι hnorm hone π)

/-- **The repair is a weakening.**  The model-first form gives the
representation-first form at once: instantiate it at the scalar model
`A n = ℂ`, `ι n z = z • 1`, whose coefficients are MF
(`Analysis/ShulmanFillNormingScalarMF.hasMFEmbedding_complex`), whose
contractivity is `norm_scalarIota_le` and whose units are the identity.

The antecedent is false — `not_theorem4ModelFirst` — so this implication is not
evidence for the consequent.  What it records is that no consumer of
`Theorem4RepresentationFirstStatement` assumes anything the refuted binder did
not already grant, so replacing the old binder by the new one weakens every
statement that used it. -/
theorem theorem4RepresentationFirst_of_modelFirst
    (h : Theorem4ModelFirstStatement) :
    Theorem4RepresentationFirstStatement := by
  intro H _ _ _ _ B _ _ hB π hπ
  obtain ⟨φ⟩ := h (fun _ : ℕ ↦ scalarIota H) (norm_scalarIota_le H)
    (tendsto_scalarIota_one H) (fun _ ↦ hasMFEmbedding_complex) B hB π hπ
  exact ⟨fun _ : ℕ ↦ ℂ, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ hasMFEmbedding_complex, fun _ : ℕ ↦ scalarIota H,
    norm_scalarIota_le H, tendsto_scalarIota_one H, ⟨φ⟩⟩

end

end ShulmanFill
end GroupApproximation
