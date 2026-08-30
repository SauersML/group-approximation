import GroupApproximation.Analysis.VoiculescuGlimmStatement

/-!
# (V2) Escaping a finite-dimensional subspace

`Analysis/VoiculescuGlimmVector` produces approximate eigenvectors of a
self-adjoint `b` as elements of the range of a continuous cut `f(b)`, with no
control over *which* element: the estimate `‖(b - μ) f(b)η‖ ≤ δ ‖f(b)η‖` holds
for every `η` at once.  Glimm's lemma needs one that also escapes a prescribed
finite-dimensional subspace, and this module supplies the freedom to choose it.

The count is the whole argument.  If a subspace `W` were to meet `Vᗮ` only in
`0`, then the orthogonal projection onto `V`, restricted to `W`, would be
injective, and `W` would embed in a finite-dimensional space — so an
infinite-dimensional `W` always contains a nonzero vector orthogonal to `V`.
Applied to `W = ` the range of `f(b)`, which is infinite-dimensional exactly
when `f(b)` is not of finite rank, this is what turns "approximate eigenvector"
into "approximate eigenvector orthogonal to `V`".

Nothing here mentions the functional calculus or the essential spectrum: it is
a statement about two subspaces, and the operator-theoretic input — that the
cut has infinite-dimensional range — is what the consumer supplies.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The dimension count.**  An infinite-dimensional subspace contains a
nonzero vector orthogonal to any finite-dimensional one.

Proved by contraposition through the projection: were the intersection with
`Vᗮ` trivial, `W ∋ w ↦ starProjection V w` would be injective into `V`. -/
theorem exists_mem_orthogonal_ne_zero {W V : Submodule ℂ H} [FiniteDimensional ℂ V]
    (hW : ¬ FiniteDimensional ℂ W) : ∃ x, x ∈ W ∧ x ∈ Vᗮ ∧ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hW ?_
  have hmem : ∀ w : W, V.starProjection (w : H) ∈ V := fun w ↦
    V.starProjection_apply_mem (w : H)
  let f : W →ₗ[ℂ] V :=
    { toFun := fun w ↦ ⟨V.starProjection (w : H), hmem w⟩
      map_add' := fun w w' ↦ by
        refine Subtype.ext ?_
        show V.starProjection ((w : H) + (w' : H))
          = V.starProjection (w : H) + V.starProjection (w' : H)
        rw [map_add]
      map_smul' := fun c w ↦ by
        refine Subtype.ext ?_
        show V.starProjection (c • (w : H)) = c • V.starProjection (w : H)
        rw [map_smul] }
  have hinj : Function.Injective f := by
    intro w w' hww
    have hcoe : V.starProjection (w : H) = V.starProjection (w' : H) :=
      congrArg (fun z : V ↦ (z : H)) hww
    have h0 : V.starProjection ((w : H) - (w' : H)) = 0 := by
      rw [map_sub, hcoe, sub_self]
    have hmemW : (w : H) - (w' : H) ∈ W := W.sub_mem w.2 w'.2
    have hmemV : (w : H) - (w' : H) ∈ Vᗮ := by
      have h := Submodule.sub_starProjection_mem_orthogonal
        (K := V) ((w : H) - (w' : H))
      rwa [h0, sub_zero] at h
    exact Subtype.ext (sub_eq_zero.mp (hcon _ hmemW hmemV))
  exact FiniteDimensional.of_injective f hinj

omit [CompleteSpace H] in
/-- **The form the vector construction consumes.**  A nonzero vector of an
infinite-dimensional subspace orthogonal to `V`, normalised. -/
theorem exists_norm_eq_one_mem_orthogonal {W V : Submodule ℂ H}
    [FiniteDimensional ℂ V] (hW : ¬ FiniteDimensional ℂ W) :
    ∃ x, x ∈ W ∧ x ∈ Vᗮ ∧ ‖x‖ = 1 := by
  obtain ⟨x, hxW, hxV, hx0⟩ := exists_mem_orthogonal_ne_zero (V := V) hW
  exact ⟨(‖x‖ : ℂ)⁻¹ • x, W.smul_mem _ hxW, Vᗮ.smul_mem _ hxV,
    norm_smul_inv_norm hx0⟩

end

end ShulmanFill
end GroupApproximation
