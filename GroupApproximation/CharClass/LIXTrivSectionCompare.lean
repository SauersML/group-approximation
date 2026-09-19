import GroupApproximation.CharClass.LIXBundleModel
import GroupApproximation.CharClass.LemmaTwoGlue
import GroupApproximation.CharClass.BundleLocal

/-!
# The trivialised section

Lane `cc-lix-odd`, the first step of `hsq`.

`hsq` compares two routes into the local model: the section read in this lane's charts, and
the bundle trivialised by `cc-bundle`'s intertwiner.  The obstruction is real — the two
sides identify the local model for different reasons, one because the base is
`2r`-real-dimensional and one because the fibre is `ℂ^r` — but the intertwiner does not
survive the comparison, and that is what makes it cheap.

**The intertwiner collapses on the section.**  `intert p x₀ x` is
`p x₀ * p x + (1 - p x₀) * (1 - p x)`, an explicit formula rather than an opaque object.
The section lies in its own fibre, so `(1 - W_g x) *ᵥ σ x = 0` and the second summand dies:

```text
intert W_g z x *ᵥ σ x  =  W_g z *ᵥ σ x
```

The trivialised section is the section **projected into the fibre at the zero**, and no
intertwiner appears in it.

This is the step that turned `hsq` from a comparison of two trivialisations into a
computation, and it came from reading `intert` rather than pricing it from its type.

## Main results

* `one_sub_mappingTorus_mulVec_lixSection` — the section is killed by the complementary
  projection at its own point.
* `intert_mulVec_lixSection` — **the collapse**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- The complementary projection kills the section at its own point. -/
theorem one_sub_mappingTorus_mulVec_lixSection
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (p : ↥sphereOne × baseM dd) :
    (1 - mappingTorus Vmat G circHoriz circHeight p) *ᵥ lixSection G p = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, lixSection_mem hGu p, sub_self]

/-- **The intertwiner collapses on the section.**  The trivialised section is the section
projected into the fibre at the zero; no intertwiner survives. -/
theorem intert_mulVec_lixSection (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (z p : ↥sphereOne × baseM dd) :
    Bundle.intert (lixBundle G hGc hGu) z p *ᵥ lixSection G p
      = mappingTorus Vmat G circHoriz circHeight z *ᵥ lixSection G p := by
  show (mappingTorus Vmat G circHoriz circHeight z
        * mappingTorus Vmat G circHoriz circHeight p
      + (1 - mappingTorus Vmat G circHoriz circHeight z)
        * (1 - mappingTorus Vmat G circHoriz circHeight p)) *ᵥ lixSection G p = _
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    lixSection_mem hGu p, one_sub_mappingTorus_mulVec_lixSection hGu p,
    Matrix.mulVec_zero, add_zero]

end GroupApproximation.CharClass
