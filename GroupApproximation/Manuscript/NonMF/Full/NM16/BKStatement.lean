import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): the finite-coordinate localization claim

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310--315 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

Lane NM16 duplicates the foreign, never-compiled `NonMF/RelatedBK` chain in
`Full/NM16`. This module states the localization principle as a named
proposition. `Full/NM16/BKLocalization` proves it outright
(`coronaUCPFiniteCoordinateLocalization`), and no downstream theorem takes it as a
hypothesis.

## Where the claim sits in the converse

`Full/NM16/BKConverse` proves "nuclear and MF implies NF" for unital C-star
algebras with this tolerance bookkeeping.

1. *Nuclear step* (`BKUnitalized`). Take `F` finite and `ε > 0`, and put
   `C = ∑_{a ∈ F} ‖a‖`. Pick `δ ≤ 1/2` with `4 (1 + C)² δ < ε`. Nuclearity
   gives a UCP map `α : A → D` and a CPC map `β : D → A` with a nontrivial
   finite-dimensional `D` and `‖β α a - a‖ ≤ δ (1 + ‖a‖)` on `S`. Here `S` is
   `F` together with the pairwise products.
2. *MF step* (`exists_unitalMFEmbedding_with_ucp_extension`). There is a
   faithful unital `π : A → Q(X)` into the cofinite norm-matrix corona, and a
   UCP `Ext : Q(X) → D` with `Ext ∘ π = α`.
3. *Lift step* (`exists_completelyPositiveContractive_finiteDimensional_lift`).
   The CPC map `π ∘ β` has a CPC lift `L : D → ∏ M_{X n}`.
4. *Tail selection* (`eventually_coord_norm_lt_of_corona_norm_lt`). From some
   coordinate `N` on, every multiplicative defect `L(α(ab)) - L(α a) L(α b)` has
   coordinate norm `< ε`.
5. *Localization* (the claim below, proved in `BKLocalization`). There are a
   star homomorphism `ρ` that only sees coordinates `≥ N` and a CPC map `θ`
   with `θ ∘ ρ ≈ Ext ∘ mk` on `{L(α a) : a ∈ F}`.
6. *Assemble.* Put `down = ρ ∘ L ∘ α` and `up = β ∘ θ`.
-/

namespace GroupApproximation.Full.NM16

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForRelatedBKLocalizationNM16
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- **Finite-coordinate localization of UCP maps out of the matrix corona.**

This is the localization step of the converse. It is proved in
`Full/NM16/BKLocalization`. Take a UCP map
`Ext : Q(X) → D` into a nontrivial finite-dimensional C-star algebra, a finite
set `T` of bounded matrix sequences, a tolerance `δ > 0` and a coordinate
threshold `N`. Then there are a matrix block `Y`, a star homomorphism `ρ` and a
completely positive contraction `θ` with these properties:

* `ρ` sees only coordinates at or after `N`: any bound valid on those
  coordinates of `x` bounds `ρ x`.
* `θ ∘ ρ` reproduces `Ext ∘ mk` within `δ` on `T`.

The module docstring gives the surrounding route. -/
def CoronaUCPFiniteCoordinateLocalizationClaim : Prop :=
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

end GroupApproximation.Full.NM16

open GroupApproximation.Full.NM16

#audit_axioms CoronaUCPFiniteCoordinateLocalizationClaim
