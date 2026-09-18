import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): the finite-coordinate localization gap

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

## Where this module sits in the proof

The RelatedBK directory proves the converse "nuclear and MF implies NF" for
unital C*-algebras, assuming one localization principle that is recorded here
as a named proposition. Here is the proof of the converse, with its tolerance
bookkeeping (see `ConverseReduction`).

1. *Nuclear step* (`UnitalizedNuclear`). Take `F` finite and `ε > 0`, and put
   `C = ∑_{a ∈ F} ‖a‖`. Pick `δ ≤ 1/2` with `4 (1 + C)² δ < ε`. Nuclearity
   gives CPC maps `α₀ : A → D` and `β : D → A` with a nontrivial
   finite-dimensional `D` and `‖β α₀ a - a‖ ≤ δ` on `S ∪ {1}`. Here `S` is `F`
   together with the pairwise products. The additive unitalization `α` of
   `α₀` is UCP, and `‖β α a - a‖ ≤ δ (1 + ‖a‖)` on `S`.
2. *MF step* (`exists_unitalMFEmbedding_with_ucp_extension`, already in the
   corpus). There is a faithful unital `π : A → Q(X)`, where
   `Q(X) = ∏ M_{X n} / ⊕ M_{X n}` is the cofinite norm-matrix corona. There is
   also a UCP `Ext : Q(X) → D` with `Ext ∘ π = α`.
3. *Lift step* (`exists_completelyPositiveContractive_finiteDimensional_lift`,
   already in the corpus). The CPC map `π ∘ β : D → Q(X)` has a CPC lift
   `L : D → ∏ M_{X n}`.
4. *Tail selection* (`eventually_coord_norm_lt_of_corona_norm_lt`, already in
   the corpus). Fix `a, b ∈ F` and put
   `z = L(α(ab)) - L(α a) L(α b)`. Its corona image is
   `π(β α(ab) - β α a · β α b)`, whose norm is at most `4 (1 + C)² δ < ε`.
   So from some coordinate `N` on, every such `z` has coordinate norm `< ε`.
5. *Localization* (the proposition below). There is a star homomorphism
   `ρ : ∏ M_{X n} → M_Y` that only sees coordinates `≥ N`, and a CPC map
   `θ : M_Y → D`, such that `θ ∘ ρ ≈ Ext ∘ mk` on the finite set
   `{L(α a) : a ∈ F}`.
6. *Assemble.* Put `down = ρ ∘ L ∘ α` and `up = β ∘ θ`. Then
   `down(ab) - down a · down b = ρ z`, which has norm `< ε` by the tail clause.
   Also `up (down a) - a` splits as
   `β(θ ρ L α a - α β α a) + β α(β α a - a) + (β α a - a)`. Its norm is
   `≤ δ + 2 δ (1 + C) ≤ 4 (1 + C)² δ < ε`.

## The isolated gap and why it is true

`CoronaUCPFiniteCoordinateLocalizationStatement` says the following. Let
`Ext : Q(X) → D` be UCP with `D` finite-dimensional, let `T` be a finite set of
bounded sequences, and fix `δ > 0` and `N`. Then there are a matrix block `Y`,
a star homomorphism `ρ` and a CPC map `θ` with these properties:

* The norm of `ρ x` is bounded by any bound valid on the coordinates `n ≥ N` of
  `x`.
* `‖θ (ρ x) - Ext (mk x)‖ ≤ δ` for `x ∈ T`.

This is the Blackadar--Kirchberg localization. A proof sketch, not formalized
in the corpus:

* Embed `D ⊆ M_d` with a conditional expectation `E : M_d → D`. The map
  `Φ = Ext ∘ mk : ∏ M_{X n} → M_d` is UCP and kills `⊕ M_{X n}`.
* By the Choi correspondence, `Φ` is given by a state `ψ` on
  `M_d(∏ M_{X n}) = ∏ M_d ⊗ M_{X n}` that vanishes on the ideal `⊕`.
* By Hahn--Banach, `ψ` is a weak* limit of convex combinations
  `∑ tᵢ ω_{ξᵢ, nᵢ}` of vector states at coordinates `nᵢ ≥ N`. Test a
  self-adjoint `h`: since `ψ` kills the ideal, `ψ(h) ≤ sup_{n ≥ N} λ_max(h_n)`.
* Such a combination is `x ↦ W* (⊕ᵢ x_{nᵢ}) W`, with `‖W‖² ≤ 1 + η` once the
  unit is in the test set.
* Take `ρ x = ⊕ᵢ x_{nᵢ}` on `Y = Σᵢ X nᵢ`, and `θ y = E(W* y W) / (1 + η)`.

The weak* approximation plus the rescaling give the `δ` estimate. Weighting
UCP coordinate maps by scalars alone does *not* suffice. The Choi and
Hahn--Banach step, which rotates vector states inside `M_d ⊗ M_{X n}`, is what
is missing from the corpus.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBK

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForRelatedBKLocalization
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- **Finite-coordinate localization of UCP maps out of the matrix corona.**

This is the single named gap of the RelatedBK converse. Take a UCP map
`Ext : Q(X) → D` into a nontrivial finite-dimensional C-star algebra, a finite
set `T` of bounded matrix sequences, a tolerance `δ > 0` and a coordinate
threshold `N`. Then there are a matrix block `Y`, a star homomorphism `ρ` and a
completely positive contraction `θ` with these properties:

* `ρ` sees only coordinates at or after `N`: any bound valid on those
  coordinates of `x` bounds `ρ x`.
* `θ ∘ ρ` reproduces `Ext ∘ mk` within `δ` on `T`.

The module docstring gives the proof route. -/
def CoronaUCPFiniteCoordinateLocalizationStatement : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (D : Type) [CStarAlgebra D] [Nontrivial D] [FiniteDimensional ℂ D]
    (Ext : NormMatrixCStarCorona (fun n ↦ X n) →ₗ[ℂ] D),
    IsCompletelyPositive Ext → Ext 1 = 1 →
      ∀ (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) (δ : ℝ), 0 < δ →
        ∀ N : ℕ,
          ∃ (Y : FiniteModel) (hY : Nonempty Y),
            letI : Nonempty Y := hY
            ∃ (ρ : BoundedMatrixSequence (fun n ↦ X n) →⋆ₙₐ[ℂ] Matrix Y Y ℂ)
              (θ : Matrix Y Y ℂ →ₗ[ℂ] D),
              (∀ (x : BoundedMatrixSequence (fun n ↦ X n)) (c : ℝ),
                  (∀ n, N ≤ n → ‖x n‖ ≤ c) → ‖ρ x‖ ≤ c) ∧
                IsCompletelyPositive θ ∧
                (∀ y : Matrix Y Y ℂ, ‖θ y‖ ≤ ‖y‖) ∧
                ∀ x ∈ T,
                  ‖θ (ρ x) - Ext (normMatrixCStarCoronaMk (fun n ↦ X n) x)‖ ≤ δ

end

end RelatedBK
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedBK

#audit_axioms CoronaUCPFiniteCoordinateLocalizationStatement
