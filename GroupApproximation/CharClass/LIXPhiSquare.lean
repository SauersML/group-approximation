import GroupApproximation.CharClass.LIXTrivSectionCompare
import GroupApproximation.CharClass.LIXFullChart
import GroupApproximation.CharClass.LIXBaseChartHomeo
import GroupApproximation.CharClass.LIXSliceEquation
import GroupApproximation.CharClass.BundleFrame

/-!
# The discrepancy map of the odd side's square

Lane `cc-lix-odd`.

`hsq` compares two routes into the local model, and they use **different** identifications
of it: `t` through this lane's charts, because the base is `2r`-real-dimensional; `loc`
through `cc-bundle`'s trivialisation, because the fibre is `ℂ^r`.  Proving the two
identifications agree is not possible, since each makes a non-canonical choice.

**The escape is to write the discrepancy into the square.**  `lixPhi` is the trivialised
section read in *both* coordinate systems at once, so it absorbs both choices and no
comparison is ever needed.  The square then holds as bookkeeping and the content moves to
`lixPhi` being an isomorphism, a statement that never mentions the Thom class and therefore
cannot re-enter the circle that the earlier reductions did.

By `intert_mulVec_lixSection` the trivialised section is the section **projected into the
fibre at the zero**, with no intertwiner surviving, which is what makes `lixPhi` writable
at all.

## This file so far

* `trace_mappingTorus_lixZero` — the rank at the zero, in the form `fibreEquivPi` takes.
* `lixPhi` — **the discrepancy map**.

`lixSquare_phi`, `lixPhi_iso` and `lixHsq` follow.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- The rank at the section's zero, in the form `fibreEquivPi` consumes. -/
theorem trace_mappingTorus_lixZero (_hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Matrix.trace (mappingTorus Vmat G circHoriz circHeight (lixZero dd))
      = ((lixRank dd : ℕ) : ℂ) := by
  show Matrix.trace (mappingTorus Vmat G circHoriz circHeight
    (southPole, lixZeroPoint dd)) = _
  rw [trace_mappingTorus_lixSlice G (lixZeroPoint dd)]
  rfl

/-- The section, projected into the fibre at the zero, lands in that fibre. -/
theorem lixSectionFibre_mem (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (p : ↥sphereOne × baseM dd) :
    mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ lixSection G p
      ∈ Bundle.fibreSet (mappingTorus Vmat G circHoriz circHeight (lixZero dd)) :=
  Bundle.mulVec_mulVec_self (lixBundle G hGc hGu) (lixZero dd) (lixSection G p)

/-- **The discrepancy map**: the trivialised section read in both coordinate systems, so
that neither identification of the local model has to be compared with the other. -/
def lixPhi (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (v : Fin (lixRank dd) → ℂ) : Fin (lixRank dd) → ℂ :=
  fibreEquivPi (isStarProjection_mappingTorus_lix hGu (lixZero dd))
      (lixRank dd) (trace_mappingTorus_lixZero hGu)
    ⟨mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ
        lixSection G (lixBaseChart dd ((lixFullChart dd).symm v)),
      lixSectionFibre_mem hGc hGu _⟩

end GroupApproximation.CharClass
