import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.KazhdanGenerators

/-!
# The Kazhdan projection as a uniform orbit-average limit

For a Kazhdan pair contained in a finite set `S` containing the identity, the
uniform orbit average contracts the orthogonal complement of the invariant
vectors by a fixed factor `c < 1`. Consequently its powers converge in
operator norm, uniformly over every orthogonal representation, to the
orthogonal projection onto the invariant vectors.

This is the constructive form of the central Kazhdan projection needed by the
weak-MF corner argument: the approximating operators are explicit finite
linear combinations of group elements, so the same polynomials can be
evaluated in finite matrix microstates.
-/

namespace GroupApproximation
namespace KazhdanProjection

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Property `(T)` supplies one finite symmetric generating Kazhdan set,
containing the identity, with tolerance in `(0,1]`.  This is the form whose
matrix orbit average is asymptotically self-adjoint and whose corner commutes
with every group element. -/
theorem HasKazhdanPropertyT.exists_symmetric_generating_pair
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ∃ S : Finset G, ∃ ε : ℝ,
      1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧
      Subgroup.closure (S : Set G) = ⊤ ∧ 0 < ε ∧ ε ≤ 1 ∧
      IsKazhdanPair.{u, u} G S ε := by
  obtain ⟨S, hone, hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset G hT
  obtain ⟨a, ha⟩ := KazhdanGenerators.exists_pair_on_generators
    hT S hsymm hgen
  let ε : ℝ := min a 1
  have hεpos : 0 < ε := lt_min ha.1 zero_lt_one
  have hεa : ε ≤ a := min_le_left _ _
  have hεone : ε ≤ 1 := min_le_right _ _
  exact ⟨S, ε, hone, hsymm, hgen, hεpos, hεone,
    IsKazhdanPair.shrink ha hεpos hεa⟩

end KazhdanProjection
end GroupApproximation
