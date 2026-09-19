import GroupApproximation.Analysis.CalkinCompactIdeal

/-!
# Schauder's theorem in Hilbert space, reduced to one residual

`Analysis/CalkinAlgebra` gets its star, and hence `Q(H)` becomes a normed star
algebra, exactly from `CompactStarClosedStatement`: the adjoint of a compact
operator is compact.  This module reduces that to a single statement about one
operator, and proves everything else.

## Which route, and why not the others

Three routes were considered against the pinned Mathlib, and two of them are
blocked by missing names rather than by difficulty.

* **Via polar decomposition** — `T` compact, `|T| = (T*T)^{1/2}` compact by the
  continuous functional calculus, `T* = |T|U*`.  Dead: Mathlib has no polar
  decomposition of a bounded operator; neither `polarDecomposition` nor
  `polar_decomposition` occurs in the library.
* **Via density of the finite-rank operators** — `T = lim Fₙ` with `Fₙ` of
  finite rank, so `T* = lim Fₙ*`.  Dead: `Analysis/Normed/Operator/Compact`
  carries no finite-rank material at all, so the density theorem would have to
  be proved first, and it is the harder of the two theorems.
* **Via `S*S`** — the route taken here.  It needs no functional calculus, no
  polar decomposition and no finite-rank theory, and it isolates a single
  clean residual.

## The route

For `S` bounded on a Hilbert space, `‖Sx‖² = ⟪S*Sx, x⟫ ≤ ‖S*Sx‖ ‖x‖`, so `S`
is compact as soon as `S*S` is; that is `CompactOfStarMulSelfStatement`, the
one residual below.  Apply it to `S = T*`: then `S*S = T T*`, which is compact
whenever `T` is, because right multiplication by a bounded operator is
precomposition (`IsCompactOperator.comp_clm`).  So `T*` is compact.

The residual is left unproved because `IsCompactOperator f` is
`∃ K, IsCompact K ∧ f ⁻¹' K ∈ 𝓝 0`, and turning the norm inequality above into
that form is a genuine argument about neighbourhoods rather than a rewrite.
It is one statement about one operator, with no amalgams, coronas or ideals in
it, and Mathlib has nothing of the shape `S*S` compact implies `S` compact.

The residual is no longer left unproved: `Analysis/CalkinSchauderProof` proves it,
so `compactStarClosed_of_compactOfStarMulSelf` is applied there and Schauder's
theorem is unconditional.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated, so the first build after the suspension
is where its names are checked.
-/

namespace GroupApproximation
namespace CalkinAlgebra

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- `T T*` is compact whenever `T` is: right multiplication by a bounded
operator is precomposition, which preserves compactness. -/
theorem isCompactOperator_mul_star (T : H →L[ℂ] H)
    (hT : IsCompactOperator T) : IsCompactOperator (T * star T) := by
  have h := hT.comp_clm (star T)
  exact h

/-- **The residual.**  On a Hilbert space, `S` is compact as soon as `S*S` is.
The proof is the estimate `‖Sx‖² = ⟪S*Sx, x⟫ ≤ ‖S*Sx‖ ‖x‖`, carried into the
neighbourhood form of `IsCompactOperator`. -/
def CompactOfStarMulSelfStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H), IsCompactOperator (star S * S) → IsCompactOperator S

/-- **Schauder's theorem in Hilbert space**, from the residual: apply it to
`T*`, whose `S*S` is `T T*`. -/
theorem compactStarClosed_of_compactOfStarMulSelf
    (h : CompactOfStarMulSelfStatement) : CompactStarClosedStatement := by
  intro H _ _ _ T hT
  refine h H (star T) ?_
  rw [star_star]
  exact isCompactOperator_mul_star T hT

end

end CalkinAlgebra
end GroupApproximation
