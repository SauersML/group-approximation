import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.EquivFin
import GroupApproximation.Kazhdan.CCKWCosetCliques

/-!
# The coset complex of `GHB(7)` is locally finite

The vertex groups `P₀ = ⟨a,b⟩`, `P₁ = ⟨c,b⟩`, `P₂ = ⟨c,a⟩` of `GHB(7)` are the images of
`U₃(7)`, `U₄(7)`, `U₄(7)` (`range_u3ToAB`, `range_u4ToCB`, `range_u4ToCA`), so they are finite
once `U₃(7)` and `U₄(7)` are (`finite_vertexGroup`).  A neighbour of the vertex `gPᵢ` is a coset
`hPⱼ` meeting `gPᵢ`, so it is `kPⱼ` for some `k ∈ gPᵢ`, `k = gp` with `p ∈ Pᵢ`: the neighbours lie
in the image of the finite set `Fin 3 × Pᵢ` under `(j, p) ↦ gpPⱼ` (`cosetComplex_locallyFinite`).
This is the local finiteness the fixed-clique theorem for the systolic complex uses in CCKW
Theorem 3.1(ii).
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

/-- **The vertex groups of `GHB(7)` are finite** once `U₃(7)` and `U₄(7)` are. -/
theorem finite_vertexGroup [Finite (U3 7)] [Finite (U4 7)] (i : Fin 3) :
    Finite (vertexGroup i) := by
  rcases fin_three_cases i with rfl | rfl | rfl
  · have h : Finite (u3ToAB 7).range :=
      Finite.of_surjective _ (u3ToAB 7).rangeRestrict_surjective
    rw [range_u3ToAB] at h
    exact h
  · have h : Finite (u4ToCB 7).range :=
      Finite.of_surjective _ (u4ToCB 7).rangeRestrict_surjective
    rw [range_u4ToCB] at h
    exact h
  · have h : Finite (u4ToCA 7).range :=
      Finite.of_surjective _ (u4ToCA 7).rangeRestrict_surjective
    rw [range_u4ToCA] at h
    exact h

/-- **The coset complex of `GHB(7)` is locally finite**: every vertex has finitely many
neighbours, once `U₃(7)` and `U₄(7)` are finite. -/
theorem cosetComplex_locallyFinite [Finite (U3 7)] [Finite (U4 7)] :
    ∀ v : Vertex, (cosetComplex.G.neighborSet v).Finite := by
  intro v
  haveI := finite_vertexGroup v.1
  obtain ⟨g, hg⟩ := CCKWTits.exists_rep v
  refine (Set.finite_range fun jp : Fin 3 × vertexGroup v.1 =>
    CCKWTits.vtx vertexGroup jp.1 (g * jp.2)).subset ?_
  intro w hw
  have hadj : cosetComplex.G.Adj v w := hw
  obtain ⟨-, k, hv, hw'⟩ := hadj
  refine ⟨(w.1, ⟨g⁻¹ * k, CCKWTits.mem_of_rep_rep hg hv⟩), ?_⟩
  show CCKWTits.vtx vertexGroup w.1 (g * (g⁻¹ * k)) = w
  rw [mul_inv_cancel_left]
  exact CCKWTits.vtx_eq_of_rep hw'

end CCKW
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.CCKW.finite_vertexGroup
#audit_axioms GroupApproximation.KMSGroup.CCKW.cosetComplex_locallyFinite
