import GroupApproximation.GroupTheory.HydeLodha.QTwoBrownCover
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's criterion for `Q₂ ≤ Γ ≤ Γ₂`

Hyde–Lodha, Theorem 4.8: "Each `Γ` satisfying `Q_n ≤ Γ ≤ Γ_n` is of type `F_∞`.  We consider the actions
of `Γ, Γ_n` on `X = ℤ[1/η_n]/ℤ`, and the natural extension of this action to that on the simplicial
complex whose `k`-simplices are the `(k+1)`-element subsets of `X`.  For each nonempty finite set
`K ⊂ X`, `Γ_{K,1}` is an extension of `Γ_{K+ℤ}` by a cyclic (trivial or infinite cyclic) group.  Since
from Proposition 4.7 `Γ_{K+ℤ}` is of type `F_∞`, it follows from applying Proposition 2.2 that
`Γ_{K,1}` is of type `F_∞`.  From Proposition 3.5, for each `k ∈ ℕ ∖ {0}`, the action of `F_{η_n}'`
on `(ℤ[1/η_n])^k` has finitely many orbits.  Hence the same holds for `Γ` since
`F_{η_n}' ≤ Q_n ≤ Γ`.  Using Theorem 2.1, we conclude that `Γ` is of type `F_∞`."

Finite presentation only needs the cells of dimension at most two, and on the single orbit of the vertex
`0 + ℤ` Brown's criterion is `DoubleCosetPresentation.isFinitelyPresented_of_doubleCosets`:

* vertex: `Γ_{{0},1}` finitely presented (`isFinitelyPresented_vertexH`, from Proposition 4.7 at `{0}`);
* edges: `Γ_{{0, t 0},1}` finitely generated (`fg_edgeStab_vertexH`, from Proposition 4.7 at `{0, t 0}`);
* finitely many orbits of edges (`vertexH_cover`) and of triangles (the hypothesis `htri`, the
  triangle case of "finitely many orbits").

`isFinitelyPresented_of_stabK_triangle` takes Proposition 4.7 and the triangle count as explicit
hypotheses; both are proved in their own modules and discharged in the endpoint module.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson DoubleCosetPresentation

/-- **Hyde–Lodha, Theorem 4.8 (finite presentation)**, from Proposition 4.7 and the triangle count. -/
theorem isFinitelyPresented_of_stabK_triangle {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ)
    (hΓ : Γ ≤ gammaTwo)
    (h47 : ∀ K : Set ℚ, K.Finite → K.Nonempty → (∀ k ∈ K, Dyadic6 k) →
      Group.IsFinitelyPresented ↥(stabK Γ K))
    (htri : ∀ t' t : ↥Γ, ∃ A : Finset ↥(vertexH Γ), ∀ a : ↥(vertexH Γ),
      ∃ c : ↥(edgeStab (vertexH Γ) t'⁻¹), ∃ d : ↥(edgeStab (vertexH Γ) t),
      ∃ a₀ ∈ A, a = (c : ↥(vertexH Γ)) * a₀ * d) :
    Group.IsFinitelyPresented ↥Γ := by
  haveI : Group.IsFinitelyPresented ↥(stabK Γ {0}) :=
    h47 {0} (Set.finite_singleton 0) (Set.singleton_nonempty 0) fun k hk => by
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      exact zero_mem_grid_six
  haveI : Group.IsFinitelyPresented ↥(vertexH Γ) := isFinitelyPresented_vertexH Γ hΓ
  obtain ⟨T, hT⟩ := vertexH_cover hQ hΓ
  refine isFinitelyPresented_of_doubleCosets (vertexH Γ) T hT (fun t _ => ?_)
    (fun t' _ t _ => htri t' t)
  haveI : Group.IsFinitelyPresented ↥(stabK Γ {0, (t : Equiv.Perm ℚ) 0}) :=
    h47 {0, (t : Equiv.Perm ℚ) 0} ((Set.finite_singleton _).insert 0) (Set.insert_nonempty _ _)
      fun k hk => by
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with rfl | rfl
        · exact zero_mem_grid_six
        · exact gammaTwo_apply_grid (hΓ t.2) zero_mem_grid_six
  exact fg_edgeStab_vertexH Γ hΓ t

#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_of_stabK_triangle

end HydeLodha
end GroupApproximation
