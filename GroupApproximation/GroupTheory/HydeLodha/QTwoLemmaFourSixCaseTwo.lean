import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Lemma 4.6, Case 2: `|I| = 1`

Hyde–Lodha, proof of Lemma 4.6: "It remains to show that `Υ_{Γ_n}(I)' ≤ ⟨f, H⟩`, which reduces to:
**Claim**: `Υ_{Γ_n}(I)' ⊆ ⋃_{n ∈ ℕ} f^n H f^{-n}`."

Case 2 (`|I| = 1`): "From Lemma 4.5, `Υ_{Γ_n}(I)'' = Υ_{Γ_n}(I)'`, ensuring that each element of
`Υ_{Γ_n}(I)'` lies in `Υ_{Γ_n}(I_1)'` for some interval `I_1 ⊂ I`, `|I_1| < 1`.  The claim is then proved
by applying the same proof as for `|I| < 1` to each such `I_1`, one by one."

Here `n = 2`, `η₂ = 6` and `I = [a, a + 1]` with `a ∈ ℤ[1/6]`.  The case is stated for an arbitrary
subgroup `N` (in the printed proof `N = ⟨f, H⟩`).  The proof for `|I| < 1` gives `Υ_{Γ₂}([c, d])' ≤ N` for
every grid interval `[c, d]` inside `(a, a + 1)`, and Case 2 turns that into `Υ_{Γ₂}(I)' ≤ N`.

* `LemmaFourSixCaseTwo`: the statement.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-- **Hyde–Lodha, proof of Lemma 4.6, Case 2** (`|I| = 1`): for `a ∈ ℤ[1/6]`, a subgroup `N` that
contains `Υ_{Γ₂}([c, d])'` for every grid interval `[c, d]` inside `(a, a + 1)` contains
`Υ_{Γ₂}([a, a + 1])'`. -/
def LemmaFourSixCaseTwo : Prop :=
  ∀ a : ℚ, (∃ M, a ∈ Grid 6 M) → ∀ N : Subgroup (Equiv.Perm ℚ),
    (∀ c d : ℚ, (∃ M, c ∈ Grid 6 M) → (∃ M, d ∈ Grid 6 M) → a < c → c < d → d < a + 1 →
      ⁅upsilon gammaTwo c d, upsilon gammaTwo c d⁆ ≤ N) →
    ⁅upsilon gammaTwo a (a + 1), upsilon gammaTwo a (a + 1)⁆ ≤ N

end HydeLodha
end GroupApproximation
