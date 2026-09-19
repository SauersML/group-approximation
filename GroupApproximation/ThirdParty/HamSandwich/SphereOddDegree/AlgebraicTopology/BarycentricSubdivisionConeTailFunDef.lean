import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AffineBarycentricSubdivision

/-!
# The cone operator for the barycentric subdivision homotopy

This file defines the affine **cone over a point** construction at the level of
the topological standard simplices, bundles it as a continuous map, extends it to
singular chains of `Δⁿ`, and proves the boundary identity

```text
∂ Cone_v(c) = c - Cone_v(∂ c)
```

in the exact degree-indexed form needed for the recursive proof that barycentric
subdivision is chain-homotopic to the identity.

For a point `v : Δⁿ` and a (continuous) `k`-simplex `τ : Δᵏ → Δⁿ`, the cone
`Cone_v(τ) : Δᵏ⁺¹ → Δⁿ` sends the new apex vertex to `v` and the remaining
vertices to the vertices of `τ`.  In barycentric coordinates, writing
`x = (t, x₁, …, x_{k+1})` for a point of `Δᵏ⁺¹`,

```text
Cone_v(τ)(x) = t · v + (1 - t) · τ( x₁/(1-t), …, x_{k+1}/(1-t) )
```

away from `t = 1`, and `= v` at `t = 1` (the apex).

This file does **not** assert the barycentric subdivision homotopy itself; it only
builds the cone operator and its boundary formula.
-/

open scoped BigOperators
open Finset

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-! ## 1. The normalized tail of a point of `Δᵏ⁺¹` -/

/-- The (un-normalized) coordinate function of the normalized tail of a point
`x : Δᵏ⁺¹`: the `i`-th coordinate is `x_{i+1} / (1 - x₀)`.  (Lean's `/0 = 0`
convention makes this total; the genuine simplex point is `coneTail` below.) -/
noncomputable def coneTailFun {k : ℕ} (x : Delta (k + 1)) : Fin (k + 1) → ℝ :=
  fun i => (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0)

/-
When `x₀ ≠ 1`, the normalized tail coordinates form a genuine point of `Δᵏ`.
-/

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
