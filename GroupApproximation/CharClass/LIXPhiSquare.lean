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

## Why the square is stated **locally**, and must be

`lixPhi` is built through `(lixFullChart dd).symm`, and a partial homeomorphism's inverse is
**junk off its target**.  So outside the chart's target `lixPhi` is an arbitrary value, and
the map-of-pairs condition `v ≠ 0 → φ v ≠ 0` is not merely unproved there but is about a
value with no meaning.  A square quantified over the whole local model therefore cannot
hold, however the geometry turns out.

`lixSquare_phi` and `lixPhi_iso` are consequently stated at the **neighbourhood** pairs,
where `φ` is a genuine homeomorphism of punctured pairs; `pull φ` is an isomorphism there
by `relCohomologyCongrPoint`, the same transport that built `lixRelModelIso`; and `lixHsq`
reaches the binder by composing with the two excisions already inside `t` and `loc`.  The
one-dimensionality step is unaffected, since the global model is still a line.

**Do not restate the square globally.**  It reads as the natural formulation and is the one
the design was first written in; it is not available.

## This file so far

* `trace_mappingTorus_lixZero` — the rank at the zero, in the form `fibreEquivPi` takes.
* `lixPhi` — **the discrepancy map**.
* `lixPhi_eq` — the map without the subtype, which is the form everything downstream uses.
* `continuousOn_lixPhi` — it is continuous **on the chart's target**, which is the largest
  set on which it means anything.

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

/-- **`lixPhi` written without the subtype.**  `fibreEquivPi` is multiplication by the
adjoint of a frame, so the whole map is a composite of linear maps and the section, and no
subtype appears.  Everything downstream uses this form. -/
theorem lixPhi_eq (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (v : Fin (lixRank dd) → ℂ) :
    lixPhi hGc hGu v
      = (stdFrame (isStarProjection_mappingTorus_lix hGu (lixZero dd)) (lixRank dd)
          (trace_mappingTorus_lixZero hGu))ᴴ *ᵥ
        (mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ
          lixSection G (lixBaseChart dd ((lixFullChart dd).symm v))) := rfl

/-- **`lixPhi` is continuous on the chart's target.**  Not globally: off that set the
inverse chart is junk, so there is nothing to be continuous about.  The only factor that is
merely `ContinuousOn` is the inverse chart. -/
theorem continuousOn_lixPhi (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    ContinuousOn (lixPhi hGc hGu) (lixFullChart dd).target := by
  have hbase : ContinuousOn
      (fun v : Fin (lixRank dd) → ℂ => lixBaseChart dd ((lixFullChart dd).symm v))
      (lixFullChart dd).target :=
    continuous_lixBaseChartFun.comp_continuousOn (lixFullChart dd).continuousOn_symm
  have hall : ContinuousOn
      (fun v : Fin (lixRank dd) → ℂ =>
        (stdFrame (isStarProjection_mappingTorus_lix hGu (lixZero dd)) (lixRank dd)
          (trace_mappingTorus_lixZero hGu))ᴴ *ᵥ
          (mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ
            lixSection G (lixBaseChart dd ((lixFullChart dd).symm v))))
      (lixFullChart dd).target := by
    have hcont : Continuous (fun m : ↥sphereOne × baseM dd =>
        (stdFrame (isStarProjection_mappingTorus_lix hGu (lixZero dd)) (lixRank dd)
          (trace_mappingTorus_lixZero hGu))ᴴ *ᵥ
          (mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ lixSection G m)) :=
      continuous_const.matrix_mulVec
        (continuous_const.matrix_mulVec (lixSection_continuous hGc hGu hGe))
    exact hcont.comp_continuousOn hbase
  exact hall.congr fun v _ => (lixPhi_eq hGc hGu v).symm

end GroupApproximation.CharClass
