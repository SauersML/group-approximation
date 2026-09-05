import GroupApproximation.CharClass.BundleChart

/-!
# Complex vector bundles in the projection model, VII: local triviality

Local triviality without a norm, without a square root and without the
continuous functional calculus.  The classical route conjugates `p x` to `p x₀`
by the *unitary* polar part of

    z(x) = p x₀ · p x + (1 - p x₀) · (1 - p x),

which needs `(1 - (p x - p x₀)²)^{-1/2}` -- so a C*-algebra, which
`Matrix ι ι ℂ` is not at the Mathlib pin (there is no norm instance on
`Matrix`), and a continuity statement for the functional calculus, which is
worse.  The observation that removes all of it: **`z(x)` itself is enough**.
It satisfies

    z(x) · p x = p x₀ · z(x),      z(x₀) = 1,

so `{x | det (z x) ≠ 0}` is an *open* neighbourhood of `x₀` on which `z` is
invertible with continuous inverse (`Continuous.matrix_det`,
`Continuous.matrix_adjugate`, `Matrix.inv_def`), and an invertible intertwiner
is all a *homeomorphism* of total spaces needs.  For the projective bundle a
non-unitary intertwiner is fine as well, because the line it produces is
renormalized: `conjNormalize a r = lineOf (a *ᵥ u)` for `r = rankOneProj u`.

The criterion `‖p x - p x₀‖ < 1` of `AlgTop/BundleCalculusProjection.lean` is a
special case: close projections have `z` near `1`, hence invertible.  Nothing
below needs the estimate.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section Local

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The intertwiner -/

/-- **The intertwiner** `z(x) = p x₀ · p x + (1 - p x₀)(1 - p x)`. -/
def intert (p : Bundle X ι) (x₀ x : X) : Matrix ι ι ℂ :=
  p x₀ * p x + (1 - p x₀) * (1 - p x)

theorem intert_def (p : Bundle X ι) (x₀ x : X) :
    intert p x₀ x = p x₀ * p x + (1 - p x₀) * (1 - p x) := rfl

theorem intert_self (p : Bundle X ι) (x₀ : X) : intert p x₀ x₀ = 1 := by
  have h : p x₀ * p x₀ = p x₀ := p.mul_self x₀
  have hexp : (1 - p x₀) * (1 - p x₀) = 1 - p x₀ - p x₀ + p x₀ * p x₀ := by noncomm_ring
  rw [intert_def, hexp, h]
  abel

/-- **The intertwining identity.**  This is the whole content of local
triviality; everything else is bookkeeping about invertibility. -/
theorem intert_mul (p : Bundle X ι) (x₀ x : X) :
    intert p x₀ x * p x = p x₀ * intert p x₀ x := by
  have hp : p x * p x = p x := p.mul_self x
  have hq : p x₀ * p x₀ = p x₀ := p.mul_self x₀
  have hL : (p x₀ * p x + (1 - p x₀) * (1 - p x)) * p x
      = p x₀ * (p x * p x) + (1 - p x₀) * (p x - p x * p x) := by noncomm_ring
  have hR : p x₀ * (p x₀ * p x + (1 - p x₀) * (1 - p x))
      = (p x₀ * p x₀) * p x + (p x₀ - p x₀ * p x₀) * (1 - p x) := by noncomm_ring
  rw [intert_def, hL, hR, hp, hq]
  simp

theorem continuous_intert (p : Bundle X ι) (x₀ : X) : Continuous (intert p x₀) :=
  (continuous_const.matrix_mul p.continuous).add
    (continuous_const.matrix_mul (continuous_const.sub p.continuous))

/-! ### The trivializing neighbourhood -/

/-- The set of points whose fibre the intertwiner identifies with the fibre over
`x₀`.  It is open and contains `x₀`. -/
def trivSet (p : Bundle X ι) (x₀ : X) : Set X := {x | (intert p x₀ x).det ≠ 0}

theorem mem_trivSet_iff {p : Bundle X ι} {x₀ x : X} :
    x ∈ trivSet p x₀ ↔ (intert p x₀ x).det ≠ 0 := Iff.rfl

theorem isOpen_trivSet (p : Bundle X ι) (x₀ : X) : IsOpen (trivSet p x₀) := by
  have h : trivSet p x₀ = (fun x => (intert p x₀ x).det) ⁻¹' ({(0 : ℂ)}ᶜ) := rfl
  rw [h]
  exact IsOpen.preimage ((continuous_intert p x₀).matrix_det) isOpen_compl_singleton

theorem self_mem_trivSet (p : Bundle X ι) (x₀ : X) : x₀ ∈ trivSet p x₀ := by
  show (intert p x₀ x₀).det ≠ 0
  rw [intert_self, Matrix.det_one]
  exact one_ne_zero

theorem isUnit_det_intert {p : Bundle X ι} {x₀ x : X} (hx : x ∈ trivSet p x₀) :
    IsUnit (intert p x₀ x).det := isUnit_iff_ne_zero.mpr hx

theorem intert_mul_inv {p : Bundle X ι} {x₀ x : X} (hx : x ∈ trivSet p x₀) :
    intert p x₀ x * (intert p x₀ x)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_intert hx)

theorem inv_mul_intert {p : Bundle X ι} {x₀ x : X} (hx : x ∈ trivSet p x₀) :
    (intert p x₀ x)⁻¹ * intert p x₀ x = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_intert hx)

theorem isUnit_det_inv_intert {p : Bundle X ι} {x₀ x : X} (hx : x ∈ trivSet p x₀) :
    IsUnit ((intert p x₀ x)⁻¹).det := by
  refine isUnit_iff_ne_zero.mpr ?_
  intro h
  have h1 : ((intert p x₀ x) * (intert p x₀ x)⁻¹).det = 1 := by
    rw [intert_mul_inv hx, Matrix.det_one]
  rw [Matrix.det_mul, h, mul_zero] at h1
  exact zero_ne_one h1

/-- The intertwining identity, read through the inverse. -/
theorem inv_intert_mul {p : Bundle X ι} {x₀ x : X} (hx : x ∈ trivSet p x₀) :
    (intert p x₀ x)⁻¹ * p x₀ = p x * (intert p x₀ x)⁻¹ := by
  have h := intert_mul p x₀ x
  calc (intert p x₀ x)⁻¹ * p x₀
      = (intert p x₀ x)⁻¹ * (p x₀ * (intert p x₀ x * (intert p x₀ x)⁻¹)) := by
        rw [intert_mul_inv hx, Matrix.mul_one]
    _ = (intert p x₀ x)⁻¹ * ((p x₀ * intert p x₀ x) * (intert p x₀ x)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = (intert p x₀ x)⁻¹ * ((intert p x₀ x * p x) * (intert p x₀ x)⁻¹) := by rw [h]
    _ = ((intert p x₀ x)⁻¹ * intert p x₀ x) * (p x * (intert p x₀ x)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = p x * (intert p x₀ x)⁻¹ := by rw [inv_mul_intert hx, Matrix.one_mul]

theorem continuous_inv_intert (p : Bundle X ι) (x₀ : X) :
    Continuous fun x : ↥(trivSet p x₀) => (intert p x₀ (x : X))⁻¹ := by
  have hcont : Continuous fun x : ↥(trivSet p x₀) => intert p x₀ (x : X) :=
    (continuous_intert p x₀).comp continuous_subtype_val
  have hdet : Continuous fun x : ↥(trivSet p x₀) => (intert p x₀ (x : X)).det :=
    hcont.matrix_det
  have hne : ∀ x : ↥(trivSet p x₀), (intert p x₀ (x : X)).det ≠ 0 := fun x => x.2
  have heq : (fun x : ↥(trivSet p x₀) => (intert p x₀ (x : X))⁻¹)
      = fun x : ↥(trivSet p x₀) =>
        ((intert p x₀ (x : X)).det)⁻¹ • (intert p x₀ (x : X)).adjugate := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [heq]
  exact (hdet.inv₀ hne).smul hcont.matrix_adjugate

/-! ### The rank is locally constant -/

theorem trace_eq_of_mem_trivSet {p : Bundle X ι} {x₀ x : X} (hx : x ∈ trivSet p x₀) :
    (p x).trace = (p x₀).trace := by
  have h : p x = (intert p x₀ x)⁻¹ * p x₀ * intert p x₀ x := by
    rw [inv_intert_mul hx, Matrix.mul_assoc, inv_mul_intert hx, Matrix.mul_one]
  calc (p x).trace = ((intert p x₀ x)⁻¹ * p x₀ * intert p x₀ x).trace := by rw [← h]
    _ = (intert p x₀ x * ((intert p x₀ x)⁻¹ * p x₀)).trace := Matrix.trace_mul_comm _ _
    _ = ((intert p x₀ x * (intert p x₀ x)⁻¹) * p x₀).trace := by simp only [Matrix.mul_assoc]
    _ = (p x₀).trace := by rw [intert_mul_inv hx, Matrix.one_mul]

theorem rank_eq_of_mem_trivSet {p : Bundle X ι} {x₀ x : X} (hx : x ∈ trivSet p x₀) :
    p.rank x = p.rank x₀ := rank_eq_of_trace_eq (trace_eq_of_mem_trivSet hx)

/-- **The rank is locally constant**, in the concrete form: every point has an
open neighbourhood on which the rank is the rank at that point. -/
theorem exists_open_rank_eq (p : Bundle X ι) (x₀ : X) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, p.rank x = p.rank x₀ :=
  ⟨trivSet p x₀, isOpen_trivSet p x₀, self_mem_trivSet p x₀,
    fun _ hx => rank_eq_of_mem_trivSet hx⟩

/-! ### A finite trivializing cover of a compact base -/

/-- **A compact base has a finite trivializing cover.**  This is the cover the
Leray-Hirsch induction of `cc-projective` runs over. -/
theorem exists_finite_trivializing_cover [CompactSpace X] (p : Bundle X ι) :
    ∃ s : Finset X, (Set.univ : Set X) ⊆ ⋃ x₀ ∈ s, trivSet p x₀ :=
  isCompact_univ.elim_finite_subcover (fun x₀ : X => trivSet p x₀)
    (fun x₀ => isOpen_trivSet p x₀)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, self_mem_trivSet p x⟩)

/-! ### The model fibres -/

/-- The fibre of the total space over a point, as a subspace of `ι → ℂ`. -/
def fibreSet (q : Matrix ι ι ℂ) : Set (ι → ℂ) := {v | q *ᵥ v = v}

/-- The fibre of the projective bundle over a point. -/
def projFibreSet (q : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {r | rᴴ = r ∧ r * r = r ∧ r.trace = 1 ∧ q * r = r}

theorem mem_totalSet_iff_mem_fibreSet {p : Bundle X ι} {v : X × (ι → ℂ)} :
    v ∈ totalSet p ↔ v.2 ∈ fibreSet (p v.1) := Iff.rfl

theorem mem_projSet_iff_mem_projFibreSet {p : Bundle X ι} {z : X × Matrix ι ι ℂ} :
    z ∈ projSet p ↔ z.2 ∈ projFibreSet (p z.1) := Iff.rfl

/-- The line spanned by a nonzero vector of the fibre is a point of the
projective fibre. -/
theorem lineOf_mem_projFibreSet {q : Matrix ι ι ℂ} {u : ι → ℂ} (hu : u ≠ 0)
    (hfix : q *ᵥ u = u) : lineOf u ∈ projFibreSet q :=
  ⟨conjTranspose_eq_of_isStarProjection (isStarProjection_lineOf hu),
    (isStarProjection_lineOf hu).isIdempotentElem.eq, trace_lineOf hu, mul_lineOf hfix⟩

/-- Every point of a projective fibre is the line spanned by a unit vector of the
fibre. -/
theorem exists_unitVector_of_mem_projFibreSet {q : Matrix ι ι ℂ} {r : Matrix ι ι ℂ}
    (hr : r ∈ projFibreSet q) :
    ∃ u ∈ unitVectors ι, r = rankOneProj u ∧ q *ᵥ u = u := by
  have hproj : IsStarProjection r := isStarProjection_matrix_iff.mpr ⟨hr.1, hr.2.1⟩
  obtain ⟨u, hu, hru⟩ := eq_rankOneProj_of_trace_one hproj hr.2.2.1
  refine ⟨u, hu, hru, ?_⟩
  have h : q * rankOneProj u = rankOneProj u := by rw [← hru]; exact hr.2.2.2
  have h2 : q *ᵥ (rankOneProj u *ᵥ u) = rankOneProj u *ᵥ u := by
    rw [Matrix.mulVec_mulVec, h]
  rwa [rankOneProj_mulVec_self hu] at h2

/-! ### The projectivized action of an invertible matrix -/

theorem conjNormalize_lineOf {κ : Type} [Fintype κ] (b : Matrix κ ι ℂ) {w : ι → ℂ}
    (hw : w ≠ 0) : conjNormalize b (lineOf w) = lineOf (b *ᵥ w) := by
  have hpos : 0 < Real.sqrt (eucNormSq w) := Real.sqrt_pos.mpr (eucNormSq_pos hw)
  have hc : (((Real.sqrt (eucNormSq w))⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (inv_pos.mpr hpos))
  rw [lineOf_eq_rankOneProj_normalizeVec hw, conjNormalize_rankOneProj, normalizeVec_eq_smul,
    Matrix.mulVec_smul, lineOf_smul hc]

theorem mulVec_ne_zero_of_isUnit {a : Matrix ι ι ℂ} (ha : IsUnit a.det) {u : ι → ℂ}
    (hu : u ≠ 0) : a *ᵥ u ≠ 0 := by
  intro h
  refine hu ?_
  have h1 : a⁻¹ *ᵥ (a *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ha, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at h1
  exact h1.symm

/-- **An invertible intertwiner moves the projective fibre.** -/
theorem conjNormalize_mem_projFibreSet {a q q' : Matrix ι ι ℂ} (ha : IsUnit a.det)
    (hint : a * q = q' * a) {r : Matrix ι ι ℂ} (hr : r ∈ projFibreSet q) :
    conjNormalize a r ∈ projFibreSet q' := by
  obtain ⟨u, hu, hru, hqu⟩ := exists_unitVector_of_mem_projFibreSet hr
  have hune : u ≠ 0 := ne_zero_of_eucNormSq_eq_one hu
  have hau : a *ᵥ u ≠ 0 := mulVec_ne_zero_of_isUnit ha hune
  rw [hru, conjNormalize_rankOneProj]
  refine lineOf_mem_projFibreSet hau ?_
  calc q' *ᵥ (a *ᵥ u) = (q' * a) *ᵥ u := Matrix.mulVec_mulVec u q' a
    _ = (a * q) *ᵥ u := by rw [hint]
    _ = a *ᵥ (q *ᵥ u) := (Matrix.mulVec_mulVec u a q).symm
    _ = a *ᵥ u := by rw [hqu]

theorem conjNormalize_conjNormalize {a : Matrix ι ι ℂ} (ha : IsUnit a.det)
    {q : Matrix ι ι ℂ} {r : Matrix ι ι ℂ} (hr : r ∈ projFibreSet q) :
    conjNormalize a⁻¹ (conjNormalize a r) = r := by
  obtain ⟨u, hu, hru, -⟩ := exists_unitVector_of_mem_projFibreSet hr
  have hune : u ≠ 0 := ne_zero_of_eucNormSq_eq_one hu
  have hau : a *ᵥ u ≠ 0 := mulVec_ne_zero_of_isUnit ha hune
  rw [hru, conjNormalize_rankOneProj, conjNormalize_lineOf _ hau, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ha, Matrix.one_mulVec, lineOf_of_mem_unitVectors hu]

/-! ### The local trivializations -/

/-- The restriction of a bundle to a subspace of the base. -/
def restrictTo (p : Bundle X ι) (U : Set X) : Bundle ↥U ι :=
  comap ⟨Subtype.val, continuous_subtype_val⟩ p

@[simp]
theorem restrictTo_apply (p : Bundle X ι) (U : Set X) (x : ↥U) :
    p.restrictTo U x = p (x : X) := rfl

/-- **Local triviality of the total space.**  Over the open set `trivSet p x₀`
the total space is the product of the base with the single fibre over `x₀`, by a
homeomorphism over the base. -/
def totalTriv (p : Bundle X ι) (x₀ : X) :
    Total (p.restrictTo (trivSet p x₀)) ≃ₜ ↥(trivSet p x₀) × ↥(fibreSet (p x₀)) where
  toFun w := ((w : ↥(trivSet p x₀) × (ι → ℂ)).1,
    ⟨intert p x₀ ((w : ↥(trivSet p x₀) × (ι → ℂ)).1 : X)
        *ᵥ (w : ↥(trivSet p x₀) × (ι → ℂ)).2, by
      show p x₀ *ᵥ (intert p x₀ _ *ᵥ _) = intert p x₀ _ *ᵥ _
      rw [Matrix.mulVec_mulVec, ← intert_mul, ← Matrix.mulVec_mulVec,
        mem_totalSet_iff.mp w.2]⟩)
  invFun w := ⟨(w.1, (intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ)), by
      show p (w.1 : X) *ᵥ ((intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ))
        = (intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ)
      rw [Matrix.mulVec_mulVec, ← inv_intert_mul w.1.2, ← Matrix.mulVec_mulVec, w.2.2]⟩
  left_inv w := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show (intert p x₀ ((w : ↥(trivSet p x₀) × (ι → ℂ)).1 : X))⁻¹
        *ᵥ (intert p x₀ ((w : ↥(trivSet p x₀) × (ι → ℂ)).1 : X)
          *ᵥ (w : ↥(trivSet p x₀) × (ι → ℂ)).2)
      = (w : ↥(trivSet p x₀) × (ι → ℂ)).2
    rw [Matrix.mulVec_mulVec, inv_mul_intert (w : ↥(trivSet p x₀) × (ι → ℂ)).1.2,
      Matrix.one_mulVec]
  right_inv w := by
    refine Prod.ext rfl ?_
    apply Subtype.ext
    show intert p x₀ (w.1 : X) *ᵥ ((intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ))
      = (w.2 : ι → ℂ)
    rw [Matrix.mulVec_mulVec, intert_mul_inv w.1.2, Matrix.one_mulVec]
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((((continuous_intert p x₀).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).matrix_mulVec
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun :=
    ((continuous_fst.prodMk
      (((continuous_inv_intert p x₀).comp continuous_fst).matrix_mulVec
        (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

theorem totalTriv_over_base (p : Bundle X ι) (x₀ : X)
    (w : Total (p.restrictTo (trivSet p x₀))) :
    (p.totalTriv x₀ w).1 = totalPi (p.restrictTo (trivSet p x₀)) w := rfl

/-- **Local triviality of the projective bundle.**  Over `trivSet p x₀` it is the
product of the base with the projective fibre over `x₀`. -/
def projTriv (p : Bundle X ι) (x₀ : X) :
    Proj (p.restrictTo (trivSet p x₀)) ≃ₜ ↥(trivSet p x₀) × ↥(projFibreSet (p x₀)) where
  toFun z := ((z : ↥(trivSet p x₀) × Matrix ι ι ℂ).1,
    ⟨conjNormalize (intert p x₀ ((z : ↥(trivSet p x₀) × Matrix ι ι ℂ).1 : X))
      (z : ↥(trivSet p x₀) × Matrix ι ι ℂ).2,
      conjNormalize_mem_projFibreSet
        (isUnit_det_intert (z : ↥(trivSet p x₀) × Matrix ι ι ℂ).1.2)
        (intert_mul p x₀ _) z.2⟩)
  invFun z := ⟨(z.1, conjNormalize (intert p x₀ (z.1 : X))⁻¹ (z.2 : Matrix ι ι ℂ)), by
      refine conjNormalize_mem_projFibreSet (isUnit_det_inv_intert z.1.2) ?_ z.2.2
      exact (inv_intert_mul z.1.2).symm⟩
  left_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact conjNormalize_conjNormalize
      (isUnit_det_intert (z : ↥(trivSet p x₀) × Matrix ι ι ℂ).1.2) z.2
  right_inv z := by
    refine Prod.ext rfl ?_
    apply Subtype.ext
    have hinv : ((intert p x₀ (z.1 : X))⁻¹)⁻¹ = intert p x₀ (z.1 : X) :=
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_intert z.1.2)
    have h := conjNormalize_conjNormalize (a := (intert p x₀ (z.1 : X))⁻¹)
      (isUnit_det_inv_intert z.1.2) z.2.2
    rwa [hinv] at h
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_conjNormalize
        ((continuous_intert p x₀).comp
          (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)))
        (continuous_snd.comp continuous_subtype_val)
        (fun z => by
          have hz := z.2
          obtain ⟨u, hu, hru, -⟩ := exists_unitVector_of_mem_projFibreSet hz
          rw [hru]
          exact (trace_conj_ne_zero_iff _ _).mpr
            (mulVec_ne_zero_of_isUnit
              (isUnit_det_intert (z : ↥(trivSet p x₀) × Matrix ι ι ℂ).1.2)
              (ne_zero_of_eucNormSq_eq_one hu)))).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk
      (continuous_conjNormalize ((continuous_inv_intert p x₀).comp continuous_fst)
        (continuous_subtype_val.comp continuous_snd)
        (fun z => by
          obtain ⟨u, hu, hru, -⟩ := exists_unitVector_of_mem_projFibreSet z.2.2
          rw [hru]
          exact (trace_conj_ne_zero_iff _ _).mpr
            (mulVec_ne_zero_of_isUnit (isUnit_det_inv_intert z.1.2)
              (ne_zero_of_eucNormSq_eq_one hu))))).subtype_mk _

theorem projTriv_over_base (p : Bundle X ι) (x₀ : X)
    (z : Proj (p.restrictTo (trivSet p x₀))) :
    (p.projTriv x₀ z).1 = projPi (p.restrictTo (trivSet p x₀)) z := rfl

end Local

end Bundle

end CharClass
end GroupApproximation
