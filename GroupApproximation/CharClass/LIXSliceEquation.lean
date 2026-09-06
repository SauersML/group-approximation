import GroupApproximation.CharClass.LIXVBundle

/-!
# The mapping torus on a polar slice

Lane `cc-lix-odd`, answering the last seam of the even side.

The question was whether the mapping torus restricted to a slice `{p₁} × {q₅} × Y` is
**equal** to `V = 𝟏³ ⊕ H` over `Y`, or only conjugate to it by a continuous unitary field
coming from the clutching.

**It is an equality, and the clutching function does not appear.**  At either pole the
horizontal coordinate vanishes, so `mtTrans (G m) 0 = 0` and `G` drops out of the formula
entirely before any of the block algebra runs.  What is left is `V` sitting in one summand
of the doubled index type:

```text
at the north pole   W_g = V ⊕ 0        at the south pole   W_g = 0 ⊕ V
```

with `lixZero`'s circle coordinate being the south pole, so the south form is the one the
slice uses.

**The one thing this is not.**  `0 ⊕ V` is not `V`: the index type is doubled.  So a value
computed for `V` transfers along the inclusion of the second summand, which is a bundle
isomorphism independent of `y`, not along an identity.  That is far weaker than a
continuous unitary field, and it needs no clutching data.

## Main results

* `mappingTorus_lixSlice` — **the slice equation**, at the south pole.
* `mappingTorus_lixSlice_north` — the north form, for a consumer preferring the first
  summand.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The poles' coordinates

Already in `MappingTorusProjection`, each by `rfl`; restated here only as a pointer, since
my first draft of this file redeclared all four and the duplicate-name check caught it
immediately.  `circHoriz_southPole`, `circHeight_southPole`, `circHoriz_northPole`,
`circHeight_northPole`. -/

/-! ## 2. The slice equation -/

/-- **The mapping torus on the south polar slice is `0 ⊕ V`, on the nose.**  The clutching
field `G` is absent: the horizontal coordinate vanishes at the pole, so it is annihilated
before the block algebra runs. -/
theorem mappingTorus_lixSlice (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (m : baseM dd) :
    mappingTorus Vmat G circHoriz circHeight (southPole, m)
      = Matrix.fromBlocks 0 0 0 (Vmat m) :=
  mappingTorus_south circHoriz_southPole circHeight_southPole m

/-- The north form, `V ⊕ 0`. -/
theorem mappingTorus_lixSlice_north (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (m : baseM dd) :
    mappingTorus Vmat G circHoriz circHeight (northPole, m)
      = Matrix.fromBlocks (Vmat m) 0 0 0 :=
  mappingTorus_north circHoriz_northPole circHeight_northPole m

/-- The slice equation in the projective coordinate alone, which is the form the even side
consumes: over `Y`, at the marked sphere point, the restricted mapping torus is `0 ⊕ V`. -/
theorem mappingTorus_lixSlice_baseY (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (y : baseY dd) :
    mappingTorus Vmat G circHoriz circHeight (southPole, ((negEThree, y) : baseM dd))
      = Matrix.fromBlocks 0 0 0 (VmatY y) := by
  rw [mappingTorus_lixSlice G ((negEThree, y) : baseM dd)]
  rw [VmatY_eq ((negEThree, y) : baseM dd)]

end GroupApproximation.CharClass
