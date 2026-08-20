import GroupApproximation.Analysis.CStarAdjointableNorm

/-!
# Unitaries between Hilbert C⋆-modules

An adjointable `U` with `U⋆U = 1` and `UU⋆ = 1`.  Two Kasparov bimodules are
*unitarily equivalent* when such a `U` intertwines their gradings,
representations and operators, and that is the first of the two relations
`KK(A,B)` is a quotient by; it is also the language in which Kasparov's
stabilization theorem `H_B ⊕ E ≅ H_B` is stated.

## What is proved

* `IsUnitaryAdj.inner_map` --- **a unitary preserves the inner product**.  This
  is not an assumption: `⟨Ux, Uy⟩ = ⟨x, U⋆Uy⟩ = ⟨x,y⟩` uses only the adjoint
  relation, so "unitary" needs only the two operator identities and never a
  separate isometry clause;
* `IsUnitaryAdj.norm_map` --- hence a unitary is isometric, hence bounded by
  `1`, with no estimate to prove;
* the groupoid structure: identities, composites and adjoints of unitaries are
  unitaries.

Neither clause of `IsUnitaryAdj` can be dropped.  `U⋆U = 1` alone is an
isometry (`inner_map` still holds), and isometries of Hilbert modules need not
be surjective; `UU⋆ = 1` alone is a coisometry.  It is the pair that gives an
isomorphism of Hilbert modules.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

namespace Adjointable

variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
variable {G : CStarModule.{v, w''} B}

/-- **A unitary**: `U⋆U = 1` and `UU⋆ = 1`, both pointwise. -/
structure IsUnitaryAdj (U : Adjointable E F) : Prop where
  /-- `U⋆U = 1`. -/
  adj_toFun : ∀ x : E.carrier, U.adj (U.toFun x) = x
  /-- `UU⋆ = 1`. -/
  toFun_adj : ∀ y : F.carrier, U.toFun (U.adj y) = y

namespace IsUnitaryAdj

variable {U : Adjointable E F}

/-- **A unitary preserves the inner product.**  A consequence of the adjoint
relation, not a third clause. -/
theorem inner_map (h : U.IsUnitaryAdj) (x y : E.carrier) :
    F.inner (U.toFun x) (U.toFun y) = E.inner x y := by
  rw [U.inner_adj, h.adj_toFun]

/-- A unitary is isometric. -/
theorem norm_map (h : U.IsUnitaryAdj) (x : E.carrier) :
    F.norm (U.toFun x) = E.norm x := by
  rw [CStarModule.norm_def, CStarModule.norm_def, h.inner_map]

theorem isBoundedBy_one (h : U.IsUnitaryAdj) : U.IsBoundedBy 1 := by
  intro x
  rw [h.norm_map, one_mul]

theorem isBounded (h : U.IsUnitaryAdj) : U.IsBounded :=
  ⟨1, zero_le_one, h.isBoundedBy_one⟩

/-- The adjoint of a unitary is a unitary. -/
theorem adjoint (h : U.IsUnitaryAdj) :
    (Adjointable.adjoint U).IsUnitaryAdj where
  adj_toFun := h.toFun_adj
  toFun_adj := h.adj_toFun

/-- A composite of unitaries is a unitary. -/
theorem comp {V : Adjointable F G} (hV : V.IsUnitaryAdj)
    (hU : U.IsUnitaryAdj) : (V.comp U).IsUnitaryAdj where
  adj_toFun x := by
    show U.adj (V.adj (V.toFun (U.toFun x))) = x
    rw [hV.adj_toFun, hU.adj_toFun]
  toFun_adj z := by
    show V.toFun (U.toFun (U.adj (V.adj z))) = z
    rw [hU.toFun_adj, hV.toFun_adj]

end IsUnitaryAdj

/-- The identity is a unitary. -/
theorem isUnitaryAdj_id (E : CStarModule.{v, w} B) :
    (Adjointable.id E).IsUnitaryAdj where
  adj_toFun _ := rfl
  toFun_adj _ := rfl

end Adjointable

end HilbertModule
end GroupApproximation
