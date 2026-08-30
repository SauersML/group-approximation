import GroupApproximation.Analysis.VoiculescuGlimmStatement

/-!
# (V2) A state that kills the compacts does not see a compact compression

Glimm's lemma is about states of `B(H)` that annihilate `K(H)`, and this is the
identity through which that hypothesis is spent:

    `ρ((1 - e) T (1 - e)) = ρ(T)`   for every compact `e` ,

exactly, not approximately.  The three error terms `T e`, `e T` and `e T e` are
compact because the compacts are an ideal, so `ρ` kills each of them.

The consequence worth stating in words: compressing by `1 - e` moves `T` a long
way in norm — that is the whole point of the compression, since it pushes `T`
towards the part of `H` that `e` does not see — while leaving `ρ(T)` fixed.  So
a bound on `‖(1 - e) T (1 - e)‖` is a bound on `|ρ(T)|` for every compact `e` at
once, which is what turns "annihilates the compacts" into a statement about the
*essential* behaviour of `T` and lets the approximate eigenvectors of
`Analysis/VoiculescuGlimmVector` be found where the state can see them.

Nothing here needs `e` to be an approximate unit, self-adjoint, or contractive:
compactness alone does it, and the identity is exact for each `e` separately
rather than in a limit.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The compression identity.**  A positive functional annihilating the
compacts is unchanged by compression by `1 - e` for any compact `e`. -/
theorem apply_compress_eq_of_annihilates_compacts
    (ρ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)
    (hρ : ∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0)
    (e T : H →L[ℂ] H) (he : IsCompactOperator e) :
    ρ ((1 - e) * T * (1 - e)) = ρ T := by
  have hexp : (1 - e) * T * (1 - e) = T - T * e - e * T + e * T * e := by
    noncomm_ring
  have h1 : ρ (T * e) = 0 := hρ _ (he.clm_comp T)
  have h2 : ρ (e * T) = 0 := hρ _ (he.comp_clm T)
  have h3 : ρ (e * T * e) = 0 := hρ _ ((he.comp_clm T).comp_clm e)
  rw [hexp, map_add, map_sub, map_sub, h1, h2, h3, sub_zero, sub_zero, add_zero]

end

end ShulmanFill
end GroupApproximation
