import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosKraus
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-27, part 4: the smaller Statement `ChoiEffrosKrausCPAP`

## Truth check of `hcpap : IsNuclearCStarAlgebra A → IsMatrixLeftBimoduleCPAP A`

The implication is **TRUE as stated**.  It is not false.

* `A` is unital, since Mathlib's `CStarAlgebra` includes a unit.
* `ρ` and `ψ` must be unital, and they can be.  `IsNuclearCStarAlgebra` gives cpc maps
  `α : A → D` and `β : D → A` through a finite-dimensional `D`.  Choi--Effros upgrades them
  to ucp maps: cut `α(1)` off spectrally, conjugate by its inverse square root on the
  support, and fill the remaining corner with a state.  The error is controlled by
  `‖βα(1) − 1‖`.
* Embed `D ≅ ⊕ M_{kᵢ}` unitally into `M_N`, block-diagonally, with a ucp conditional
  expectation `E : M_N → D`.  Put `ρ = ι ∘ α` and `ψ = β ∘ E`.  Both are ucp, so they are
  contractive, preserve stars, and satisfy rank-one positivity.
* The left bimodule clause is Choi's inequality
  `‖ψ(xM) − ψ(x)ψ(M)‖ ≤ ‖ψ(xx⋆) − ψ(x)ψ(x)⋆‖^{1/2} ‖M‖`.  Apply it at `x = ρ(a)`, together with
  the Schwarz-defect estimate below.
* For trivial `A`, take `Y` empty.

None of Choi--Effros, the structure theorem, the conditional expectation, Stinespring/Choi
decomposition or Choi's inequality is in the corpus.

## The smaller Statement

`ChoiEffrosKrausCPAP` is `IsMatrixLeftBimoduleCPAP`, with three changes:

1. `ψ` is given in **Kraus-column form** `ψ = ψ_G`, where `G : Y → A`.  The four algebraic
   clauses on `ψ` are then **proved** (`ChoiEffrosKraus`): linearity, star preservation,
   rank-one positivity, and `ψ 1 = ⟨G, G⟩ = 1`.
2. `ψ_G` is contractive.
3. The left bimodule clause `∀ a ∈ F, ∀ M, …`, quantified over all matrices, is replaced by
   the **single-element Schwarz defect** `‖ψ(ρ a ρ a⋆) − ψ(ρ a) ψ(ρ a)⋆‖ ≤ δ` for `a ∈ F`.
   The bimodule clause is **proved** from it by Choi's inequality in the column Hilbert module
   (`ChoiEffrosChoiInequality`).

**Strictly smaller in proof content.**  Every clause is a statement about a single `a ∈ F`
or a single matrix `M`, with no product between `a` and an arbitrary `M`.  The analytic core
of the target is Choi's Cauchy--Schwarz inequality for ucp maps, and it is proved here.  What
remains is purely existential structure theory: Choi--Effros, and the Choi/Stinespring form of
a ucp map on `M_Y`.

**Why it is true.**  Take ucp `ρ₀ : A → M_Y` and ucp `ψ₀ : M_Y → A` as above, approximating on
`F ∪ F F⋆` to `η`.

* **Kraus form.**  The Choi matrix `[ψ₀(e_{ij})] ∈ M_Y(A)` is positive, so it equals `B⋆B`.
  Amplify to `Y × Y`, with `ρ = ρ₀ ⊗ 1` (still ucp) and `G(i, k) = B_{k i}`.  Then
  `ψ_G(ρ₀(a) ⊗ 1) = ψ₀(ρ₀ a)`, and `ψ_G(1) = ψ₀(1) = 1`.  Also `ψ_G = G⋆(· ⊗ 1)G` is ucp, hence
  contractive.
* **Schwarz defect.**  Kadison--Schwarz for `ρ` gives `ρ(a)ρ(a)⋆ ≤ ρ(aa⋆)`.  With
  Kadison--Schwarz for `ψ`,
  `0 ≤ ψ(ρa ρa⋆) − ψρa (ψρa)⋆ ≤ ψρ(aa⋆) − ψρa (ψρa)⋆`, whose norm is `O(η(1 + ‖a‖))`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **ucp matrix factorizations with a Kraus-column `ψ` and small Schwarz defects.**  For every
finite `F` and every `δ > 0` there are:

* a unital completely positive contraction `ρ : A → M_Y` that preserves stars;
* a column `G : Y → A` with `⟨G, G⟩ = 1` whose Kraus map `ψ_G` is contractive;

such that `ψ_G ρ ≈ id` on `F`, and the Schwarz defect of `ψ_G` at `ρ a` is at most `δ` for
`a ∈ F`.  It is strictly smaller in proof content than `IsMatrixLeftBimoduleCPAP`, and it is
true for nuclear `A`; see the module docstring. -/
def ChoiEffrosKrausCPAP (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (δ : ℝ), 0 < δ →
    ∃ (Y : FiniteModel) (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (G : Y → A),
      ρ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑ρ ∧ (∀ a : A, ‖ρ a‖ ≤ ‖a‖) ∧
      (∀ a : A, ρ (star a) = star (ρ a)) ∧
      choiEffrosPair G G = 1 ∧
      (∀ M : Matrix Y Y ℂ, ‖choiEffrosKrausMap G M‖ ≤ ‖M‖) ∧
      (∀ a ∈ F, ‖choiEffrosKrausMap G (ρ a) - a‖ ≤ δ) ∧
      (∀ a ∈ F, ‖choiEffrosKrausMap G (ρ a * star (ρ a)) -
          choiEffrosKrausMap G (ρ a) * star (choiEffrosKrausMap G (ρ a))‖ ≤ δ)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosKrausCPAP

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
