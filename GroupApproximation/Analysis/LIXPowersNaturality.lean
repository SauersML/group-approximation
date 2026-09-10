import GroupApproximation.Analysis.LIXPowersGauge

/-!
# Naturality of clutching along a suspended sphere map

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3 item 3.  The Step-C computation for `v^k`
needs the projection clutched by `u ∘ ψ_k` to be the *pullback* of the projection clutched
by `u` along the suspension `Σψ_k`, where `Σψ_k` acts on the equatorial coordinates of
`S^{2n+1}` and fixes the clutching coordinate `Re (x n)`.

## The one structure that makes this a triviality

A self-map `ψ` of the unit sphere of `E` has to be extended to `E` before the clutching
layer can see it, because the layer speaks only through `coneMat`, which reads a clutching
function along rays.  The right extension is the *positively homogeneous, norm-preserving*
one, and it is worth naming:

```lean
structure IsRadialMap (Ψ : E → E) where
  continuous : Continuous Ψ
  norm_map   : ∀ y, ‖Ψ y‖ = ‖y‖
  map_smul   : ∀ r, 0 ≤ r → ∀ y, Ψ (r • y) = r • Ψ y
```

With that, the *cone* of `ψ` is `Ψ` itself, so no cone has to be built and no suspension
bookkeeping has to be done: `coneMat Ω (Ψ y) = coneMat (Ω ∘ Ψ) y` is `coneMat_comp_radial`,
three rewrites.  The suspension of `ψ` on `S^{2n+1}` is then the chart map
`(t, ν) ↦ (t, Ψ ∘ ν)` -- the clutching coordinate is fixed *by construction*, not by a
lemma -- and `isSuspensionChart_comp_radial` says the pulled-back pair is again a
suspension chart.

The recommended `ψ_k`, the *join power* `(z, v) ↦ (z^k/|z|^{k-1}, v)` of
`notes/lix-stronger-lane-reports/sp-powers.md` §0, is radial on the nose: `|z^k/|z|^{k-1}|`
is `|z|`, which is exactly `norm_map`, and the formula is positively homogeneous of degree
one.  Any other `ψ_k` has to be presented as an `IsRadialMap` to be usable here; that is
the interface this lane asks `sp-design` for.

## Main results

* `coneMat_comp_radial` -- the cone of a composite.
* `isSuspensionChart_comp_radial` -- the suspended chart.
* `clutchMat_comp_radial` -- **naturality**: `clutch (Ω ∘ Ψ)` over `(t, ν)` is
  `clutch Ω` over `(t, Ψ ∘ ν)`.
* `clutchMat_comp_radial_pullback` -- the same, transported along any realisation of
  `Σψ` as an honest self-map `Φ` of the parameter space: `clutch (Ω ∘ Ψ) x` is literally
  `clutch Ω (Φ x)`.
* `splitSusp` -- the tautological realisation of `Σψ` on `SplitSphere E`.
* `isDiscUnitary_comp_radial` -- a disc unitary precomposed with a radial map is a disc
  unitary.  This is what makes the gauge lemma survive the substitution `u ↦ u ∘ ψ_k`,
  and hence what lets the seam generator be renormalised before the powers argument runs.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n] {Ψ Φ : E → E}

/-- A **radial map**: continuous, norm-preserving and positively homogeneous.  It is the
canonical extension to `E` of a self-map of the unit sphere, and it is its own cone. -/
structure IsRadialMap (Ψ : E → E) : Prop where
  continuous : Continuous Ψ
  norm_map : ∀ y : E, ‖Ψ y‖ = ‖y‖
  map_smul : ∀ r : ℝ, 0 ≤ r → ∀ y : E, Ψ (r • y) = r • Ψ y

theorem IsRadialMap.map_zero (h : IsRadialMap Ψ) : Ψ 0 = 0 := by
  have h0 := h.map_smul 0 le_rfl 0
  rw [zero_smul, zero_smul] at h0
  exact h0

theorem isRadialMap_id : IsRadialMap (fun y : E => y) :=
  ⟨continuous_id, fun _ => rfl, fun _ _ _ => rfl⟩

theorem IsRadialMap.comp (h1 : IsRadialMap Ψ) (h2 : IsRadialMap Φ) :
    IsRadialMap fun y => Ψ (Φ y) where
  continuous := h1.continuous.comp h2.continuous
  norm_map := fun y => by rw [h1.norm_map, h2.norm_map]
  map_smul := fun r hr y => by rw [h2.map_smul r hr, h1.map_smul r hr]

theorem IsRadialMap.mapsTo_ball (h : IsRadialMap Ψ) {y : E} (hy : ‖y‖ ≤ 1) :
    ‖Ψ y‖ ≤ 1 := by rw [h.norm_map]; exact hy

/-- **The cone of a composite.**  Because a radial map is its own cone, precomposing a
clutching function with it is the same as moving the point. -/
theorem coneMat_comp_radial (hΨ : IsRadialMap Ψ) (Ω : E → Matrix n n ℂ) (y : E) :
    coneMat Ω (Ψ y) = coneMat (fun z => Ω (Ψ z)) y := by
  rw [coneMat_def, coneMat_def, hΨ.norm_map y,
    hΨ.map_smul _ (inv_nonneg.mpr (norm_nonneg y)) y]

/-- A ball unitary precomposed with a radial map is a ball unitary. -/
theorem IsBallUnitary.compRadial {Ω : E → Matrix n n ℂ} (hΩ : IsBallUnitary Ω)
    (hΨ : IsRadialMap Ψ) : IsBallUnitary fun y => Ω (Ψ y) where
  continuous := hΩ.continuous.comp hΨ.continuous
  star_mul_self := fun _ hy => hΩ.star_mul_self _ (hΨ.mapsTo_ball hy)
  mul_star_self := fun _ hy => hΩ.mul_star_self _ (hΨ.mapsTo_ball hy)

/-- **A disc unitary precomposed with a radial map is a disc unitary.**  This is what
makes a renormalisation of the seam generator survive the substitution `u ↦ u ∘ ψ_k`: if
`u = a·ũ` with `a` a disc unitary then `u ∘ ψ_k = (a ∘ ψ_k)·(ũ ∘ ψ_k)` with `a ∘ ψ_k`
again a disc unitary, so the gauge lemma applies on both sides of the substitution. -/
theorem isDiscUnitary_comp_radial {Ω : E → Matrix n n ℂ} (hΩ : IsDiscUnitary Ω)
    (hΨ : IsRadialMap Ψ) : IsDiscUnitary fun y => Ω (Ψ y) where
  continuous := hΩ.continuous.comp hΨ.continuous
  map_zero := by rw [hΨ.map_zero, hΩ.map_zero]
  star_mul_self := fun _ hy => hΩ.star_mul_self _ (hΨ.mapsTo_ball hy)
  mul_star_self := fun _ hy => hΩ.mul_star_self _ (hΨ.mapsTo_ball hy)

end Radial

/-! ## The suspended chart and naturality -/

section Naturality

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n]
  {t : X → ℝ} {ν : X → E} {Ψ : E → E}

/-- **The suspension of a radial map, as a suspension chart.**  The height -- the
clutching coordinate -- is untouched; only the equatorial part moves.  This is the
statement "`Σψ` acts on the equatorial coordinates and fixes `Re (x n)`", and it needs no
proof beyond `norm_map`. -/
theorem isSuspensionChart_comp_radial (hc : IsSuspensionChart t ν) (hΨ : IsRadialMap Ψ) :
    IsSuspensionChart t fun x => Ψ (ν x) where
  continuous_height := hc.continuous_height
  continuous_equator := hΨ.continuous.comp hc.continuous_equator
  sphere := fun x => by rw [hΨ.norm_map]; exact hc.sphere x

/-- **Naturality of clutching.**  The projection clutched by `Ω ∘ Ψ` over the chart
`(t, ν)` is the projection clutched by `Ω` over the suspended chart `(t, Ψ ∘ ν)`. -/
theorem clutchMat_comp_radial (hΨ : IsRadialMap Ψ) (Ω : E → Matrix n n ℂ) (x : X) :
    clutchMat (t x) (coneMat (fun z => Ω (Ψ z)) (ν x))
      = clutchMat (t x) (coneMat Ω (Ψ (ν x))) := by
  rw [coneMat_comp_radial hΨ]

/-- **Naturality of clutching, as a pullback.**  If the suspension `Σψ` is realised as an
honest self-map `Φ` of the parameter space -- fixing the height and moving the equatorial
part by `Ψ` -- then the projection clutched by `Ω ∘ Ψ` at `x` is literally the projection
clutched by `Ω` at `Φ x`.  This is the form the Step-C computation consumes: the section
data of the twisted bundle is the section data of the untwisted one, read at `Σψ_k x`. -/
theorem clutchMat_comp_radial_pullback (hΨ : IsRadialMap Ψ) (Ω : E → Matrix n n ℂ)
    {Φ : X → X} (hΦt : ∀ x, t (Φ x) = t x) (hΦν : ∀ x, ν (Φ x) = Ψ (ν x)) (x : X) :
    clutchMat (t x) (coneMat (fun z => Ω (Ψ z)) (ν x))
      = clutchMat (t (Φ x)) (coneMat Ω (ν (Φ x))) := by
  rw [hΦt, hΦν, coneMat_comp_radial hΨ]

/-- The untwisted projection is unchanged by the suspension: only the height and the norm
of the equatorial part enter it, and `Ψ` preserves both. -/
theorem clutchUntwisted_comp_radial (hΨ : IsRadialMap Ψ) (x : X) :
    clutchMat (t x) (((‖Ψ (ν x)‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = clutchMat (t x) (((‖ν x‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) := by
  rw [hΨ.norm_map]

end Naturality

/-! ## The tautological realisation of the suspension -/

section SplitSusp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : E → E}

/-- **The suspension `Σψ` on the split sphere.**  It moves the equatorial coordinate by
`Ψ` and leaves the height -- the clutching coordinate -- alone. -/
def splitSusp (hΨ : IsRadialMap Ψ) (p : SplitSphere E) : SplitSphere E :=
  ⟨(Ψ p.val.1, p.val.2), by
    rw [hΨ.norm_map]
    exact p.property⟩

theorem splitSusp_fst (hΨ : IsRadialMap Ψ) (p : SplitSphere E) :
    (splitSusp hΨ p).val.1 = Ψ p.val.1 := rfl

theorem splitSusp_snd (hΨ : IsRadialMap Ψ) (p : SplitSphere E) :
    (splitSusp hΨ p).val.2 = p.val.2 := rfl

theorem continuous_splitSusp (hΨ : IsRadialMap Ψ) : Continuous (splitSusp hΨ) := by
  refine Continuous.subtype_mk ?_ _
  exact (hΨ.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)

/-- The tautological chart of `SplitSphere E` is pulled back by `splitSusp` exactly as
`isSuspensionChart_comp_radial` describes: the height is fixed and the equatorial part is
moved by `Ψ`.  Both identities are definitional; they are recorded so that a lane owning a
concrete model of `S^{2n+1}` can check its own `Σψ` against them. -/
theorem splitSusp_chart (hΨ : IsRadialMap Ψ) (p : SplitSphere E) :
    (splitSusp hΨ p).val.2 = p.val.2 ∧ (splitSusp hΨ p).val.1 = Ψ p.val.1 :=
  ⟨rfl, rfl⟩

end SplitSusp

end

end Powers
end LIX
end GroupApproximation
