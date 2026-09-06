import GroupApproximation.CharClass.BundleZeroSection
import GroupApproximation.CharClass.BundleFrame
import GroupApproximation.CharClass.BundleHomotopy

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
def totalComap (f : C(Y, X)) (p : Bundle X ι) : C(Total (comap f p), Total p) where
  toFun v := ⟨(f (v : Y × (ι → ℂ)).1, (v : Y × (ι → ℂ)).2), v.2⟩
  continuous_toFun :=
    ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem totalPi_comp_totalComap (f : C(Y, X)) (p : Bundle X ι) :
    (totalPi p).comp (totalComap f p) = f.comp (totalPi (comap f p)) := rfl

/-- The map of projective bundles covering `f`. -/
def projComap (f : C(Y, X)) (p : Bundle X ι) : C(Proj (comap f p), Proj p) where
  toFun z := ⟨(f (z : Y × Matrix ι ι ℂ).1, (z : Y × Matrix ι ι ℂ).2), z.2⟩
  continuous_toFun :=
    ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem projPi_comp_projComap (f : C(Y, X)) (p : Bundle X ι) :
    (projPi p).comp (projComap f p) = f.comp (projPi (comap f p)) := rfl

/-- The map of total spaces preserves the zero section in both directions. -/
theorem totalComap_snd_eq_zero_iff (f : C(Y, X)) (p : Bundle X ι) (v : Total (comap f p)) :
    (totalComap f p v : X × (ι → ℂ)).2 = 0 ↔ (v : Y × (ι → ℂ)).2 = 0 := Iff.rfl

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

/-- `Unit × Y` is `Y`.  (Mathlib has no `Homeomorph` for this at the pin.) -/
def unitProdHomeo (Y : Type) [TopologicalSpace Y] : Unit × Y ≃ₜ Y where
  toFun q := q.2
  invFun y := ((), y)
  left_inv q := by
    cases q with
    | mk u y => cases u; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

/-- **The trivial bundle over a point**: its total space is `ℂ^r`. -/
noncomputable def totalTrivUnit (r : ℕ) : Total (triv Unit (Fin r)) ≃ₜ (Fin r → ℂ) :=
  (totalTrivHomeo).trans (unitProdHomeo (Fin r → ℂ))

theorem totalTrivUnit_eq_zero_iff (r : ℕ) (w : Total (triv Unit (Fin r))) :
    totalTrivUnit r w = 0 ↔ (w : Unit × (Fin r → ℂ)).2 = 0 := Iff.rfl

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

/-- **(C1b) the excision pair.**  The affine chart carries `E(p) ∖ 0` onto the
part of the chart that misses the zero section, so
`(E(p), E(p) ∖ 0) ⊆ (P(p ⊕ 1), P(p ⊕ 1) ∖ Z)` is a pair of opens. -/
theorem totalHomeoChart_mem_notZeroSet_iff (p : Bundle X ι) (w : Total p) :
    ((totalHomeoChart p w : Chart p) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ∈ notZeroSet p
      ↔ (w : X × (ι → ℂ)) ∈ puncturedSet p := by
  show (chartOf p w : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ∈ notZeroSet p ↔ _
  rw [chartOf_mem_notZeroSet_iff]
  exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩

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

/-- **(C3) the trivializing chart as a pair.** -/
theorem totalTrivStd_image_punctured (p : Bundle X ι) (x₀ : X) (r : ℕ) (hr : p.rank x₀ = r) :
    (totalTrivStd p x₀ r hr) ''
        {w : Total (p.restrictTo (trivSet p x₀)) |
          (w : ↥(trivSet p x₀) × (ι → ℂ)) ∈ puncturedSet (p.restrictTo (trivSet p x₀))}
      = {q : ↥(trivSet p x₀) × (Fin r → ℂ) | q.2 ≠ 0} := by
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact fun h => hw.2 ((totalTrivStd_snd_eq_zero_iff p x₀ r hr w).mp h)
  · intro hq
    refine ⟨(totalTrivStd p x₀ r hr).symm q, ⟨((totalTrivStd p x₀ r hr).symm q).2, ?_⟩,
      (totalTrivStd p x₀ r hr).apply_symm_apply q⟩
    intro h
    refine hq ?_
    rw [← (totalTrivStd p x₀ r hr).apply_symm_apply q]
    exact (totalTrivStd_snd_eq_zero_iff p x₀ r hr _).mpr h

end TrivPair

/-! ### The sphere and the punctured space of a trivial bundle -/

section TrivialSphere

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A condition on the second factor alone cuts a product out of a subtype.

Named for the second projection rather than for the product, because
`CharClass.prodSubtypeHomeo` is cc-cohom-api's older declaration of the same
theorem in the preimage vocabulary (`Prod.snd ⁻¹' S`), and a file at bare
`CharClass` that opens `Bundle` would otherwise see the bare name as
ambiguous. -/
def sndSubtypeHomeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (S : Set B) :
    ↥{v : A × B | v.2 ∈ S} ≃ₜ A × ↥S where
  toFun v := ((v : A × B).1, ⟨(v : A × B).2, v.2⟩)
  invFun q := ⟨(q.1, (q.2 : B)), q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem sphereSet_triv :
    sphereSet (triv X ι) = {v : X × (ι → ℂ) | v.2 ∈ unitVectors ι} := by
  ext v
  constructor
  · intro hv
    exact hv.2
  · intro hv
    refine ⟨?_, hv⟩
    show (1 : Matrix ι ι ℂ) *ᵥ v.2 = v.2
    exact Matrix.one_mulVec _

/-- **The sphere bundle of a trivial bundle is the product with the unit
sphere of the fibre.** -/
noncomputable def sphereTrivHomeo : Sphere (triv X ι) ≃ₜ X × ↥(unitVectors ι) :=
  (Homeomorph.setCongr sphereSet_triv).trans (sndSubtypeHomeo (unitVectors ι))

theorem sphereTrivHomeo_fst (v : Sphere (triv X ι)) :
    (sphereTrivHomeo v).1 = (v : X × (ι → ℂ)).1 := rfl

/-- **The punctured total space of a trivial bundle is the product with the
punctured fibre.** -/
noncomputable def puncturedTrivHomeo :
    Punctured (triv X ι) ≃ₜ X × ↥({v : ι → ℂ | v ≠ 0}) :=
  (Homeomorph.setCongr puncturedSet_triv).trans (sndSubtypeHomeo {v : ι → ℂ | v ≠ 0})

theorem puncturedTrivHomeo_fst (v : Punctured (triv X ι)) :
    (puncturedTrivHomeo v).1 = (v : X × (ι → ℂ)).1 := rfl

/-- **`X × (ℂ^ι ∖ 0)` is homotopy equivalent to `X × S(ℂ^ι)`**, for every base
`X` at once.

This is `puncturedHomotopyEquivSphere` at the trivial bundle, read through the
two product presentations: the equivalence normalizes the second coordinate and
leaves the first alone.  It is the input a Gysin or Thom argument needs in order
to replace the pair `(X × ℂ^r, X × (ℂ^r ∖ 0))` by `(X × ℂ^r, X × S^{2r-1})`, at
which point the long exact sequence of the pair together with an ABSOLUTE
Kunneth for a sphere factor computes the pair -- no relative Kunneth and no
hypothesis on `X` are needed. -/
noncomputable def prodPuncturedHomotopyEquivSphere :
    ContinuousMap.HomotopyEquiv (X × ↥({v : ι → ℂ | v ≠ 0})) (X × ↥(unitVectors ι)) :=
  ((puncturedTrivHomeo (X := X) (ι := ι)).symm.toHomotopyEquiv.trans
      (puncturedHomotopyEquivSphere (triv X ι))).trans
    (sphereTrivHomeo (X := X) (ι := ι)).toHomotopyEquiv

end TrivialSphere

/-! ### The fibre inclusion, as a strict map of pairs -/

section SliceIncl

/-- **The slice `{a} × B` of a product**, as a map `B → A × B`.  For a trivial
bundle presented as a product this is the inclusion of the fibre over `a`. -/
def sliceIncl {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (a : A) : C(B, A × B) :=
  (ContinuousMap.const B a).prodMk (ContinuousMap.id B)

@[simp]
theorem sliceIncl_apply {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B) :
    sliceIncl a b = (a, b) := rfl

/-- **The second projection retracts the slice inclusion**, on the nose.  This is
the identity that makes pullback along the projection injective, so that a class
pulled back from the fibre cannot vanish. -/
theorem snd_comp_sliceIncl {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (a : A) :
    (ContinuousMap.snd : C(A × B, B)).comp (sliceIncl a) = ContinuousMap.id B := rfl

/-- **The slice inclusion is a STRICT map of pairs** against any condition on the
second factor: the preimage of the subspace is that condition itself, not merely
contained in it.  Stated as a preimage equation rather than a membership, so it
drops into a relative-cohomology functoriality lemma with no conversion. -/
theorem sliceIncl_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (S : Set B) : sliceIncl a ⁻¹' {v : A × B | v.2 ∈ S} = S := rfl

/-- The projection is a strict map of pairs the other way. -/
theorem snd_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (S : Set B) :
    (ContinuousMap.snd : C(A × B, B)) ⁻¹' S = {v : A × B | v.2 ∈ S} := rfl

theorem sliceIncl_mapsTo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (S : Set B) : Set.MapsTo (sliceIncl a) S {v : A × B | v.2 ∈ S} :=
  fun _ hb => hb

theorem snd_mapsTo {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (S : Set B) :
    Set.MapsTo (ContinuousMap.snd : C(A × B, B)) {v : A × B | v.2 ∈ S} S :=
  fun _ hv => hv

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The fibre inclusion against the trivial bundle's own punctured set, so the
pair statement is available without first rewriting through
`puncturedSet_triv`. -/
theorem sliceIncl_preimage_puncturedSet_triv (x : X) :
    sliceIncl (B := ι → ℂ) x ⁻¹' puncturedSet (triv X ι) = {w : ι → ℂ | w ≠ 0} := by
  ext w
  constructor
  · intro hw
    exact hw.2
  · intro hw
    refine ⟨?_, hw⟩
    show (1 : Matrix ι ι ℂ) *ᵥ w = w
    exact Matrix.one_mulVec _

theorem sliceIncl_preimage_totalSet_triv (x : X) :
    sliceIncl (B := ι → ℂ) x ⁻¹' totalSet (triv X ι) = (Set.univ : Set (ι → ℂ)) := by
  rw [totalSet_triv]
  rfl

end SliceIncl

end Bundle

end CharClass
end GroupApproximation
