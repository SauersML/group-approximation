import GroupApproximation.Analysis.GroupVonNeumannTrace
import GroupApproximation.Analysis.ReducedGroupCStarSpan
import Mathlib.Algebra.Star.Unitary
import GroupApproximation.Meta.AxiomGuard

/-!
# The group sits in the unitary group of its von Neumann algebra

Infrastructure of lane `oa-mcduff` for `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93,
"Brown's formulation", tex 280–283 (census row `97438886a277`): "... `L(G) ⊗̄ 𝓡` is a McDuff factor
that embeds in `𝓡^ω` and whose unitary group contains `G`".  This module proves the first half of
the last clause, that `G` is a subgroup of the unitary group of `L(G)`; the amplification
`x ↦ x ⊗ 1` into `L(G) ⊗̄ 𝓡` carries it on.

* `leftRegularOperator_injective`: distinct group elements give distinct left translations,
  because `λ(g)δ₁ = δ_g`.
* `leftRegularUnitaryHom`: `g ↦ λ(g)` as a group homomorphism into the unitary group of `L(G)`.
* `leftRegularUnitaryHom_injective`: it is injective.
-/

namespace GroupApproximation
namespace GroupVonNeumann

open ReducedGroupCStarTrace

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance unitaryGroupDecEq : DecidableEq G := Classical.decEq G

/-- **Distinct group elements give distinct left translations.** -/
theorem leftRegularOperator_injective : Function.Injective (leftRegularOperator G) := by
  intro g h hgh
  by_contra hne
  have h1 : (leftRegularOperator G g (deltaOne G)) g = (leftRegularOperator G h (deltaOne G)) g := by
    rw [hgh]
  rw [leftRegularOperator_deltaOne, leftRegularOperator_deltaOne, lp.single_apply_self,
    lp.single_apply_ne 2 h 1 hne] at h1
  exact one_ne_zero h1

/-- `λ(g)` is a unitary of `L(G)`. -/
theorem leftRegularOperator_mem_unitary (g : G) :
    (⟨leftRegularOperator G g, leftRegularOperator_mem G g⟩ :
        ↥(groupVonNeumannAlgebra G).toStarSubalgebra) ∈
      unitary ↥(groupVonNeumannAlgebra G).toStarSubalgebra := by
  rw [Unitary.mem_iff]
  constructor
  · apply Subtype.ext
    change star (leftRegularOperator G g) * leftRegularOperator G g = 1
    rw [star_leftRegularOperator, leftRegularOperator_mul, inv_mul_cancel, leftRegularOperator_one]
  · apply Subtype.ext
    change leftRegularOperator G g * star (leftRegularOperator G g) = 1
    rw [star_leftRegularOperator, leftRegularOperator_mul, mul_inv_cancel, leftRegularOperator_one]

/-- **The left regular representation into the unitary group of `L(G)`.** -/
def leftRegularUnitaryHom : G →* unitary ↥(groupVonNeumannAlgebra G).toStarSubalgebra where
  toFun g := ⟨⟨leftRegularOperator G g, leftRegularOperator_mem G g⟩,
    leftRegularOperator_mem_unitary G g⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change leftRegularOperator G 1 = 1
    rw [leftRegularOperator_one]
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change leftRegularOperator G (g * h) = leftRegularOperator G g * leftRegularOperator G h
    rw [leftRegularOperator_mul]

theorem coe_leftRegularUnitaryHom (g : G) :
    (((leftRegularUnitaryHom G g : unitary ↥(groupVonNeumannAlgebra G).toStarSubalgebra) :
        ↥(groupVonNeumannAlgebra G).toStarSubalgebra) : GroupHilbert G →L[ℂ] GroupHilbert G) =
      leftRegularOperator G g :=
  rfl

/-- **`G` is a subgroup of the unitary group of `L(G)`.** -/
theorem leftRegularUnitaryHom_injective : Function.Injective (leftRegularUnitaryHom G) := by
  intro g h hgh
  apply leftRegularOperator_injective G
  rw [← coe_leftRegularUnitaryHom G g, ← coe_leftRegularUnitaryHom G h, hgh]

end

end GroupVonNeumann
end GroupApproximation

#audit_axioms GroupApproximation.GroupVonNeumann.leftRegularUnitaryHom_injective
