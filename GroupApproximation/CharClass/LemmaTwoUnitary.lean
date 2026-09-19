import GroupApproximation.Analysis.LIXObstructionComplementUnitary
import GroupApproximation.CharClass.LemmaTwoZero

/-!
# Step A feeds Step B: from the manuscript's complement equivalence to a corner unitary

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Steps A–B).

`Analysis/LIXObstructionComplementUnitary.lean` (lane `lix-obstruction`/`cs-clutching`)
delivers `STW59.exists_continuous_corner_unitary_apply_eq`: from a continuous field of
partial isometries witnessing the Murray–von Neumann equivalence of the two
complementary projections `V - e eᴴ` and `V - s sᴴ`, a continuous field of unitaries `g`
of the corner `V (Matrix K K ℂ) V`, with `g *ᵥ e = s`.

This file discharges `CharClass/MappingTorusProjection.lean`'s `IsCornerUnitary`
hypothesis from that output: `cornerExtend V g := g + (1 - V)` extends the corner
unitary to a unitary of the full matrix algebra commuting with `V`
(`isCornerUnitary_cornerExtend`), and the seam identity survives the extension because
`(1 - V) *ᵥ e = 0` whenever `V *ᵥ e = e`. This is exactly what Step B's mapping torus
`W_g` and its section (`LemmaTwoZero.lean`) consume as the transition matrix.

## Main result

* `exists_isCornerUnitary_of_stepA` — Step A's continuous partial-isometry data yields a
  continuous `G` with `∀ m, IsCornerUnitary (V m) (G m)` and `∀ m, G m *ᵥ e m = s m`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **The corner extension preserves the seam identity.**  Since `(1 - V) *ᵥ e = 0`
whenever `e` is a unit section of `V` (`V *ᵥ e = e`), `cornerExtend V g` acts on `e`
exactly as `g` does. -/
theorem cornerExtend_mulVec_eq {V g : Matrix K K ℂ} {e s : K → ℂ}
    (hVe : V *ᵥ e = e) (hge : g *ᵥ e = s) : cornerExtend V g *ᵥ e = s := by
  rw [cornerExtend, Matrix.add_mulVec, hge, Matrix.sub_mulVec, Matrix.one_mulVec, hVe,
    sub_self, add_zero]

/-- **Step A feeds Step B.**  From `cs-clutching`'s continuous corner-unitary output
(`STW59.exists_continuous_corner_unitary_apply_eq`), produce a continuous field `G` of
unitaries of the *full* matrix algebra `Matrix K K ℂ` commuting with `V` — an
`IsCornerUnitary` field, exactly what `MappingTorusProjection.lean`'s `mappingTorus`
consumes — together with the seam condition `G *ᵥ e = s`. -/
theorem exists_isCornerUnitary_of_stepA {M : Type*} [TopologicalSpace M] (k0 : K)
    {V : M → Matrix K K ℂ} {e s : M → K → ℂ}
    (hVcont : Continuous V) (hVproj : ∀ m, IsStarProjection (V m))
    (hVe : ∀ m, V m *ᵥ e m = e m) (hVs : ∀ m, V m *ᵥ s m = s m)
    (hecont : Continuous e) (hscont : Continuous s)
    (he1 : ∀ m, ∑ i, star (e m i) * e m i = 1) (hs1 : ∀ m, ∑ i, star (s m i) * s m i = 1)
    (w₁ : M → Matrix K K ℂ) (hw₁cont : Continuous w₁)
    (hw₁src : ∀ m, (w₁ m)ᴴ * w₁ m = V m - GroupApproximation.STW59.colAt k0 (e m) *
      (GroupApproximation.STW59.colAt k0 (e m))ᴴ)
    (hw₁rng : ∀ m, w₁ m * (w₁ m)ᴴ = V m - GroupApproximation.STW59.colAt k0 (s m) *
      (GroupApproximation.STW59.colAt k0 (s m))ᴴ)
    (hw₁pi : ∀ m, w₁ m * (w₁ m)ᴴ * w₁ m = w₁ m) :
    ∃ G : M → Matrix K K ℂ, Continuous G ∧
      (∀ m, IsCornerUnitary (V m) (G m)) ∧ (∀ m, G m *ᵥ e m = s m) := by
  obtain ⟨g, hgcont, hgV, hVg, hgg, hgg', hge⟩ :=
    GroupApproximation.STW59.exists_continuous_corner_unitary_apply_eq k0 hVproj hVe hVs
      hecont hscont he1 hs1 w₁ hw₁cont hw₁src hw₁rng hw₁pi
  refine ⟨fun m => cornerExtend (V m) (g m), hgcont.add (continuous_const.sub hVcont),
    fun m => isCornerUnitary_cornerExtend (hVproj m) (hgV m) (hVg m) (hgg m) (hgg' m),
    fun m => cornerExtend_mulVec_eq (hVe m) (hge m)⟩

end GroupApproximation.CharClass
