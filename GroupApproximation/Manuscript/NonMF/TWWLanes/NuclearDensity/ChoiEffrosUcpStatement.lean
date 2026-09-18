import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosKraus
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-28c, part 3: the Statement `ChoiEffrosUcpKrausStatement`

## Truth check of the target `∀ A, IsNuclear A → ChoiEffrosKrausCPAP A`

The target is **TRUE**.  The argument is the one in the `ChoiEffrosStatement` docstring:

1. Choi--Effros upgrades the cpc factorization to ucp maps `ρ₀ : A → M_Y` and `ψ₀ : M_Y → A`.
2. The structure theorem and a conditional expectation let `D` be `M_Y` itself.
3. The Choi matrix of `ψ₀` factors as `B⋆B`.  Amplifying to `Y × Y` gives a Kraus column `G`.

It **cannot be proved outright here**.  Choi--Effros, the structure theorem, the conditional
expectation and the Choi/Stinespring factorization are all absent from the corpus.

## The Statement

`ChoiEffrosUcpKrausStatement A` keeps four clauses of `ChoiEffrosKrausCPAP A`:

* `ρ` is unital;
* `ρ` is completely positive;
* `⟨G, G⟩ = 1`;
* `ψ_G ρ ≈ id` on `F`.

It **drops four clauses**, which `choiEffrosKrausCPAP_of_ucpKraus` proves:

* `ρ` is contractive (`ucp_norm_le`);
* `ρ` preserves stars (`ucp_map_star`);
* `ψ_G` is contractive (`choiEffrosUcp_norm_krausMap_le`, from positivity of `ψ_G` plus
  Cauchy--Schwarz);
* the Schwarz-defect bound.  This comes from Kadison--Schwarz for `ρ`, run on `F ∪ F F⋆` at a
  rescaled tolerance (`choiEffrosUcp_schwarzDefect_le`).

**LOUD: equivalent, not strictly weaker in logical strength.**  `ChoiEffrosKrausCPAP A` implies
`ChoiEffrosUcpKrausStatement A` trivially, by dropping clauses.  With the reduction proved, the
two are **logically equivalent** for every `A`.  The new Statement is strictly smaller only in
**proof content**: it contains no analytic clause.  What it asks for is pure structure theory,
namely:

* ucp approximate factorization through a matrix algebra (Choi--Effros);
* the Kraus-column form of the ucp map `M_Y → A` (Choi/Stinespring).

## Remaining gap

`∀ A, IsNuclear A → ChoiEffrosUcpKrausStatement A`.  This is Choi--Effros plus the Kraus form of
a ucp map on `M_Y`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **ucp matrix factorizations with a Kraus-column `ψ`, with only the four structural clauses.**
For every finite `F` and every `δ > 0` there are a unital completely positive `ρ : A → M_Y` and
a column `G : Y → A` with `⟨G, G⟩ = 1` such that `ψ_G ρ ≈ id` on `F` to within `δ`.  It is
equivalent to `ChoiEffrosKrausCPAP A` (see `choiEffrosKrausCPAP_of_ucpKraus`), and it is smaller
in proof content. -/
def ChoiEffrosUcpKrausStatement (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (δ : ℝ), 0 < δ →
    ∃ (Y : FiniteModel) (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (G : Y → A),
      ρ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑ρ ∧ choiEffrosPair G G = 1 ∧
      ∀ a ∈ F, ‖choiEffrosKrausMap G (ρ a) - a‖ ≤ δ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosUcpKrausStatement

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
