import GroupApproximation.TypeA2.Cover
import GroupApproximation.TypeA2.GeoFStabilizer
import GroupApproximation.TypeA2.HalfLineOrbits

/-!
# Normalizer covers of geometric `F` on the positive dyadic rationals

`isTypeA2_halfLineCover`: let `φ : H →* Sym(ℚ)` take values in the normalizer of `geoF 0` and
preserve the positive dyadic rationals, with `H` finitely presented.  Then the cover
`geoF 0 ⋊ H ↷ halfLineDyadics` is of type [A₂].  The inputs on `geoF 0` are finite presentation
(`geoF_isFinitelyPresented`), finitely generated point stabilizers (`geoF_zero_stabilizer_fg`) and
three orbits on pairs (`geoF_zero_orbits_pairs`).
-/

open MulAction

namespace GroupApproximation.TypeA2

open HigmanThompson

/-- **The half-line cover is of type [A₂].** -/
theorem isTypeA2_halfLineCover {H : Type} [Group H] [Group.IsFinitelyPresented H]
    (φ : H →* Equiv.Perm ℚ) (hφ : ∀ h, φ h ∈ Subgroup.normalizer (geoF 0 : Set (Equiv.Perm ℚ)))
    (hφS : ∀ h, ∀ x ∈ halfLineDyadics, φ h x ∈ halfLineDyadics) :
    IsTypeA2 (geoF 0 ⋊[coverConj (geoF 0) φ hφ] H)
      (coverSubMulAction (geoF 0) φ hφ halfLineDyadics (fun _ hg _ hx => geoF_zero_mapsTo hg hx)
        hφS) := by
  haveI := geoF_isFinitelyPresented 0
  exact isTypeA2_cover (geoF 0) φ hφ halfLineDyadics _ hφS ⟨1, one_pos, 0, one_mem_grid_mTwo 0 0⟩
    (fun _ hx => geoF_zero_stabilizer_fg hx.2 hx.1) geoF_zero_orbits_pairs

end GroupApproximation.TypeA2
