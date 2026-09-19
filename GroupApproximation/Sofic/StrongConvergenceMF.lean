import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Sofic.OperatorMF

/-!
# The strong-convergence convention for MF groups

Both manuscripts print the same remark about a second convention in the
literature.  `non_mf_groups_exist.tex`:

> The strong convergence convention of [GaoEtAl, Schafhauser] also requires the
> models to reproduce the operator norms of the left regular representation, so
> a group that is not MF as defined here is not MF in that convention either.

and `mf_recognition_complexity.tex` says the same in different words.  The
clause after "so" is an assertion, not an aside: it is the implication that
lets a non-MF theorem proved in the present sense be quoted against the other
convention.  Neither census could grade it, because nothing in the development
defined the other convention.  This file does.

## What is formalized

`IsStronglyOperatorMF` is the present notion together with the extra
requirement the convention adds: the matrix models reproduce the norms of the
left regular representation on every finitely supported complex combination of
group elements.  `leftRegularNorm` is the norm they are required to reproduce,
computed where the left regular representation actually lives, inside the
reduced group C-star algebra.

The printed implication is then a projection, which is exactly what "also
requires" means, and `not_isStronglyOperatorMF_of_not_isOperatorMF` states the
contrapositive because the contrapositive is the sentence the manuscripts
print.

Nothing else in the development consumes this convention, and nothing should:
the papers cite it once each, to say that their negative results survive the
change of convention.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- **The norm the strong-convergence convention asks the models to
reproduce.**  For a finitely supported `c : G →₀ ℂ`, the norm of the
corresponding operator of the left regular representation, computed inside the
reduced group C-star algebra. -/
noncomputable def leftRegularNorm (c : G →₀ ℂ) : ℝ :=
  ‖∑ g ∈ c.support, c g • reducedLeftRegular G g‖

/-- **The strong-convergence convention**, as
[GaoEtAl, Schafhauser] state it: an operator-norm MF model family that
*additionally* reproduces the norms of the left regular representation.

The first component is the present notion together with a coordinate lift of
its embedding, and the second is the extra requirement.  Writing the
convention this way is what the manuscripts' "also requires" says, and it is
why the implication below is a projection rather than an argument. -/
def IsStronglyOperatorMF (G : Type u) [Group G] : Prop :=
  ∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
    ∃ V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ,
      (∃ rho : G →* NormMatrixCoronaUnitary X,
          Function.Injective rho ∧
            ∀ g, QuotientGroup.mk (fun n ↦ V n g) = rho g) ∧
        ∀ c : G →₀ ℂ,
          Tendsto (fun n ↦ ‖∑ g ∈ c.support,
              c g • (V n g : Matrix (X n) (X n) ℂ)‖)
            atTop (nhds (leftRegularNorm c))

/-- The strong-convergence convention implies the present one: it asks for
everything the present one asks for, and more. -/
theorem IsStronglyOperatorMF.isOperatorMF (h : IsStronglyOperatorMF G) :
    IsOperatorMF G := by
  obtain ⟨X, hX, _V, ⟨rho, hrho, -⟩, -⟩ := h
  exact ⟨X, hX, rho, hrho⟩

/-- **The printed sentence.**  "A group that is not MF as defined here is not
MF in that convention either."  Stated as the contrapositive because the
contrapositive is what the manuscripts print and what they use: a negative
result proved in the present sense survives the change of convention. -/
theorem not_isStronglyOperatorMF_of_not_isOperatorMF
    (h : ¬ IsOperatorMF G) : ¬ IsStronglyOperatorMF G :=
  fun hs ↦ h hs.isOperatorMF

end GroupApproximation
