import GroupApproximation.CharClass.BundleZeroSection
import GroupApproximation.CharClass.BundleFrame

/-!
# Complex vector bundles in the projection model, X: pairs and pullbacks

Four small statements that the Thom-class lane consumes, none of which needs a
new idea; they are recorded here so that the consumer does not have to
rediscover that each is definitional.

* **Pullback on the spaces.**  `comap f p y` is *by definition* `p (f y)`, so the
  fibre condition over `y` and the fibre condition over `f y` are the same
  proposition and the map of total spaces is the identity on second components.
* **The trivial bundle.**  `triv`'s fibre condition is `1 *ᵥ v = v`, which is
  vacuous, so the total space of a trivial bundle is the whole product.
* **The affine chart is a map of pairs.**  `E(p) ∖ 0` corresponds to
  `(P(p⊕1) ∖ P(p)) ∖ Z` under the chart, because the `ι`-block trace of the line
  through `(v, 1)` is `‖v‖² / (1 + ‖v‖²)`.
* **The standard trivialization is a map of pairs.**  Both of its two stages are
  injective on the fibre, so a vector is zero exactly when its image is.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### Pullback on the total and projective spaces -/

section Pullback

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : Type} [Fintype ι]

/-- The map of total spaces covering `f`.  The membership proof is the identity:
`comap f p y` is `p (f y)` by definition. -/
def comapTotal (f : C(Y, X)) (p : Bundle X ι) : C(Total (comap f p), Total p) where
  toFun v := ⟨(f (v : Y × (ι → ℂ)).1, (v : Y × (ι → ℂ)).2), v.2⟩
  continuous_toFun :=
    ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem totalPi_comp_comapTotal (f : C(Y, X)) (p : Bundle X ι) :
    (totalPi p).comp (comapTotal f p) = f.comp (totalPi (comap f p)) := rfl

/-- The map of projective bundles covering `f`. -/
def comapProj (f : C(Y, X)) (p : Bundle X ι) : C(Proj (comap f p), Proj p) where
  toFun z := ⟨(f (z : Y × Matrix ι ι ℂ).1, (z : Y × Matrix ι ι ℂ).2), z.2⟩
  continuous_toFun :=
    ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem projPi_comp_comapProj (f : C(Y, X)) (p : Bundle X ι) :
    (projPi p).comp (comapProj f p) = f.comp (projPi (comap f p)) := rfl

/-- The map of total spaces preserves the zero section in both directions. -/
theorem comapTotal_snd_eq_zero_iff (f : C(Y, X)) (p : Bundle X ι) (v : Total (comap f p)) :
    (comapTotal f p v : X × (ι → ℂ)).2 = 0 ↔ (v : Y × (ι → ℂ)).2 = 0 := Iff.rfl

end Pullback

/-! ### The trivial bundle -/

section Trivial

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem totalSet_triv : totalSet (triv X ι) = (Set.univ : Set (X × (ι → ℂ))) := by
  ext v
  simp only [Set.mem_univ, iff_true]
  show (1 : Matrix ι ι ℂ) *ᵥ v.2 = v.2
  exact Matrix.one_mulVec _

/-- **The total space of a trivial bundle is the product.**  With `X` a point
this is the rank-`#ι` trivial bundle's total space `ℂ^ι`. -/
noncomputable def totalTrivHomeo : Total (triv X ι) ≃ₜ X × (ι → ℂ) :=
  (Homeomorph.setCongr totalSet_triv).trans (Homeomorph.Set.univ (X × (ι → ℂ)))

theorem puncturedSet_triv :
    puncturedSet (triv X ι) = {v : X × (ι → ℂ) | v.2 ≠ 0} := by
  ext v
  constructor
  · intro hv
    exact hv.2
  · intro hv
    refine ⟨?_, hv⟩
    show (1 : Matrix ι ι ℂ) *ᵥ v.2 = v.2
    exact Matrix.one_mulVec _

end Trivial

/-! ### The affine chart as a map of pairs -/

section ChartPair

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [TopologicalSpace X] in
theorem zTrace_lineOf_eq_zero (x : X) {v : ι ⊕ Unit → ℂ} (hv : v ≠ 0)
    (hvl : v ∘ Sum.inl = 0) :
    zTrace ((x, lineOf v) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) = 0 := by
  rw [lineOf_eq_rankOneProj_normalizeVec hv, zTrace_of_rankOneProj]
  have h : (normalizeVec v) ∘ Sum.inl
      = (((Real.sqrt (eucNormSq v))⁻¹ : ℝ) : ℂ) • (v ∘ Sum.inl) := rfl
  rw [h, hvl, smul_zero, eucNormSq_eq_zero_iff.mpr rfl, Complex.ofReal_zero]

/-- **The chart is a map of pairs.**  `E(p) ∖ 0` is carried onto the part of the
chart that misses the zero section, so `(E(p), E(p) ∖ 0)` sits inside
`(P(p ⊕ 1), P(p ⊕ 1) ∖ Z)` as an open pair. -/
theorem chartOf_mem_notZeroSet_iff (p : Bundle X ι) (v : Total p) :
    (chartOf p v : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ∈ notZeroSet p
      ↔ (v : X × (ι → ℂ)).2 ≠ 0 := by
  constructor
  · intro h hv0
    refine h.2 ?_
    have hcv : chartVec (v : X × (ι → ℂ)) ∘ Sum.inl = 0 := by
      rw [chartVec_comp_inl]
      exact hv0
    exact zTrace_lineOf_eq_zero _ (chartVec_ne_zero _) hcv
  · intro hv
    refine ⟨(chartOf p v).2.1, ?_⟩
    have hcv : chartVec (v : X × (ι → ℂ)) ∘ Sum.inl ≠ 0 := by
      rw [chartVec_comp_inl]
      exact hv
    exact zTrace_lineOf_ne_zero _ (chartVec_ne_zero _) hcv

end ChartPair

/-! ### The standard trivialization as a map of pairs -/

section TrivPair

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [TopologicalSpace X] [DecidableEq ι] in
theorem fibreEquivPi_eq_zero_iff {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (r : ℕ)
    (hr : q.trace = (r : ℂ)) (v : ↥(fibreSet q)) :
    fibreEquivPi hq r hr v = 0 ↔ (v : ι → ℂ) = 0 := by
  constructor
  · intro h
    have h2 := congrArg (fibreEquivPi hq r hr).symm h
    rw [Homeomorph.symm_apply_apply] at h2
    rw [h2]
    show stdFrame hq r hr *ᵥ (0 : Fin r → ℂ) = 0
    exact Matrix.mulVec_zero _
  · intro h
    show (stdFrame hq r hr)ᴴ *ᵥ (v : ι → ℂ) = 0
    rw [h, Matrix.mulVec_zero]

/-- **The standard local trivialization is a map of pairs**: it carries the
complement of the zero section onto `U × (ℂ^r ∖ 0)`. -/
theorem totalTrivStd_snd_eq_zero_iff (p : Bundle X ι) (x₀ : X) (r : ℕ) (hr : p.rank x₀ = r)
    (w : Total (p.restrictTo (trivSet p x₀))) :
    (totalTrivStd p x₀ r hr w).2 = 0
      ↔ (w : ↥(trivSet p x₀) × (ι → ℂ)).2 = 0 := by
  have hq : (p x₀).trace = (r : ℂ) := by rw [trace_eq_rank, hr]
  have hval : (totalTrivStd p x₀ r hr w).2
      = fibreEquivPi (p.isStarProjection x₀) r hq ((p.totalTriv x₀ w).2) := rfl
  rw [hval, fibreEquivPi_eq_zero_iff]
  constructor
  · intro h
    have h2 : intert p x₀ ((w : ↥(trivSet p x₀) × (ι → ℂ)).1 : X)
        *ᵥ (w : ↥(trivSet p x₀) × (ι → ℂ)).2 = 0 := h
    by_contra hne
    exact mulVec_ne_zero_of_isUnit
      (isUnit_det_intert (w : ↥(trivSet p x₀) × (ι → ℂ)).1.2) hne h2
  · intro h
    show intert p x₀ ((w : ↥(trivSet p x₀) × (ι → ℂ)).1 : X)
      *ᵥ (w : ↥(trivSet p x₀) × (ι → ℂ)).2 = 0
    rw [h, Matrix.mulVec_zero]

end TrivPair

end Bundle

end CharClass
end GroupApproximation
