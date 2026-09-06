import GroupApproximation.CharClass.BundleClassify

/-!
# Complex vector bundles in the projection model, XII: stabilised classifying maps

The Euler class of a line bundle is `e(L) = f_L^* h` for the classifying map
`f_L : X → ℂP^d` of `BundleClassify.classifyOne`.  For that to be an invariant of
the isomorphism class one needs isomorphic bundles to have homotopic classifying
maps, and in `ℂP^d` itself that is false in general: the two embeddings of a
line into a fixed `ℂ^{d+1}` need not be connected by a path of isometries.  It
becomes true after **one stabilisation**, along a linear isometric embedding
`ℂ^{d+1} ↪ ℂ^{N+1}` with room for two disjoint copies.

That is what this file proves.  The rotation is

    v ↦ ((1-t)·A v, t·B φ v),

conjugation by `stabRot t x = (1-t)·A + t·(B ∘ φ x)` followed by
`conjNormalize`, which is defined throughout because the trace of the conjugate
is `(1-t)² + t² > 0`.  The hypotheses on `A` and `B` are exactly that each is an
isometry and that their ranges are orthogonal, which is what a splitting
`ℂ^{N+1} ⊇ ℂ^{d+1} ⊕ ℂ^{d+1}` provides; `sumInclLeft`/`sumInclRight` build such
a pair from any equivalence `Fin (d+1) ⊕ Fin (d+1) ≃ Fin (N+1)`, for instance
`finSumFinEquiv` with `N = 2d + 1`.

Applying the rotation twice, once to the isomorphism and once to the identity,
gives the form the Euler class actually consumes: the **same** embedding on both
sides (`homotopic_cpEmbed_same`).

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59
open unitInterval

namespace Bundle

/-! ### The map of projective spaces induced by an isometry -/

section Embed

variable {d N : ℕ}

theorem cpEmbed_mem (V : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ) (hV : Vᴴ * V = 1) (z : CP d) :
    V * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ ∈ cpSet N := by
  obtain ⟨hz1, hz2, hz3⟩ := z.2
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hz1,
      Matrix.mul_assoc]
  · calc V * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ *
          (V * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ)
        = V * ((z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            ((Vᴴ * V) * ((z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = V * ((z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            ((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
              ((z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ))) := by rw [hV]
      _ = V * (((z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) * Vᴴ) := by
          simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = V * ((z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ) := by rw [hz2]
      _ = V * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm]
    calc (Vᴴ * (V * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ))).trace
        = ((Vᴴ * V) * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).trace := by rw [hV, Matrix.one_mul]
      _ = 1 := hz3

/-- **The map `ℂP^d → ℂP^N` induced by a linear isometric embedding**
`V : ℂ^{d+1} → ℂ^{N+1}`, namely `q ↦ V q Vᴴ`. -/
def cpEmbed (V : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ) (hV : Vᴴ * V = 1) : C(CP d, CP N) where
  toFun z := ⟨V * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ, cpEmbed_mem V hV z⟩
  continuous_toFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
      continuous_const).subtype_mk _

@[simp]
theorem cpEmbed_apply (V : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ) (hV : Vᴴ * V = 1) (z : CP d) :
    (cpEmbed V hV z : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
      = V * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Vᴴ := rfl

theorem mem_cpSet_of_mem_projFibreSet_one {r : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (h : r ∈ projFibreSet (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) : r ∈ cpSet N :=
  ⟨h.1, h.2.1, h.2.2.1⟩

end Embed

/-! ### The rotation -/

section Stabilize

variable {X : Type} [TopologicalSpace X] {d N : ℕ}
variable {p q : Bundle X (Fin (d + 1))}

/-- The rotating family `(1-t)·A + t·(B φ)`. -/
noncomputable def stabRot (e : BundleIso p q) (A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ)
    (t : ℝ) (x : X) : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ :=
  ((1 - t : ℝ) : ℂ) • A + ((t : ℝ) : ℂ) • (B * e.hom x)

theorem stabRot_def (e : BundleIso p q) (A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ)
    (t : ℝ) (x : X) :
    stabRot e A B t x = ((1 - t : ℝ) : ℂ) • A + ((t : ℝ) : ℂ) • (B * e.hom x) := rfl

theorem stabRot_conjTranspose (e : BundleIso p q)
    (A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ) (t : ℝ) (x : X) :
    (stabRot e A B t x)ᴴ
      = ((1 - t : ℝ) : ℂ) • Aᴴ + ((t : ℝ) : ℂ) • ((e.hom x)ᴴ * Bᴴ) := by
  rw [stabRot_def, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, star_ofReal', star_ofReal']

theorem stabRot_conjTranspose_mul (e : BundleIso p q)
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) (t : ℝ) (x : X) :
    (stabRot e A B t x)ᴴ * stabRot e A B t x
      = (((1 - t) * (1 - t) : ℝ) : ℂ) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
        + ((t * t : ℝ) : ℂ) • p x := by
  have h1 : (((1 - t : ℝ) : ℂ) • Aᴴ) * (((1 - t : ℝ) : ℂ) • A)
      = (((1 - t) * (1 - t) : ℝ) : ℂ) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, ← Complex.ofReal_mul]
  have h2 : (((1 - t : ℝ) : ℂ) • Aᴴ) * (((t : ℝ) : ℂ) • (B * e.hom x)) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hAB, Matrix.zero_mul,
      smul_zero]
  have h3 : (((t : ℝ) : ℂ) • ((e.hom x)ᴴ * Bᴴ)) * (((1 - t : ℝ) : ℂ) • A) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hBA, Matrix.mul_zero,
      smul_zero]
  have h4 : (((t : ℝ) : ℂ) • ((e.hom x)ᴴ * Bᴴ)) * (((t : ℝ) : ℂ) • (B * e.hom x))
      = ((t * t : ℝ) : ℂ) • p x := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul]
    congr 1
    calc (e.hom x)ᴴ * Bᴴ * (B * e.hom x)
        = (e.hom x)ᴴ * ((Bᴴ * B) * e.hom x) := by simp only [Matrix.mul_assoc]
      _ = (e.hom x)ᴴ * e.hom x := by rw [hB, Matrix.one_mul]
      _ = p x := e.conjTranspose_mul x
  rw [stabRot_conjTranspose, stabRot_def, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    h1, h2, h3, h4, add_zero, zero_add]

theorem trace_stabRot_conj (e : BundleIso p q)
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) (hp : ∀ x, (p x).trace = 1) (t : ℝ) (x : X) :
    (stabRot e A B t x * p x * (stabRot e A B t x)ᴴ).trace
      = (((1 - t) * (1 - t) + t * t : ℝ) : ℂ) := by
  rw [Matrix.trace_mul_comm]
  calc ((stabRot e A B t x)ᴴ * (stabRot e A B t x * p x)).trace
      = (((stabRot e A B t x)ᴴ * stabRot e A B t x) * p x).trace := by
        simp only [Matrix.mul_assoc]
    _ = (((((1 - t) * (1 - t) : ℝ) : ℂ) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
          + ((t * t : ℝ) : ℂ) • p x) * p x).trace := by
        rw [stabRot_conjTranspose_mul e hA hB hAB hBA]
    _ = ((((1 - t) * (1 - t) : ℝ) : ℂ) • p x + ((t * t : ℝ) : ℂ) • p x).trace := by
        rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, p.mul_self]
    _ = (((1 - t) * (1 - t) + t * t : ℝ) : ℂ) := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hp x]
        simp

theorem stabCoeff_pos (t : ℝ) : 0 < (1 - t) * (1 - t) + t * t := by
  nlinarith [sq_nonneg (2 * t - 1)]

theorem trace_stabRot_conj_ne_zero (e : BundleIso p q)
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) (hp : ∀ x, (p x).trace = 1) (t : ℝ) (x : X) :
    (stabRot e A B t x * p x * (stabRot e A B t x)ᴴ).trace ≠ 0 := by
  rw [trace_stabRot_conj e hA hB hAB hBA hp t x]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (stabCoeff_pos t))

theorem stabRot_conj_mem (e : BundleIso p q)
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) (hp : ∀ x, (p x).trace = 1) (t : ℝ) (x : X) :
    conjNormalize (stabRot e A B t x) (p x) ∈ cpSet N := by
  refine mem_cpSet_of_mem_projFibreSet_one
    (conjNormalize_mem_projFibreSet' (q := (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) ?_ ?_
      (trace_stabRot_conj_ne_zero e hA hB hAB hBA hp t x))
  · intro u _
    exact Matrix.one_mulVec _
  · exact ⟨p.conjTranspose_eq x, p.mul_self x, hp x, Matrix.one_mul _⟩

/-- **Isomorphic line bundles have homotopic classifying maps after one
stabilisation**, with the two block embeddings on the two sides. -/
noncomputable def stabHomotopy (e : BundleIso p q)
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (q x).trace = 1) :
    ContinuousMap.Homotopy ((cpEmbed A hA).comp (classifyOne p hp))
      ((cpEmbed B hB).comp (classifyOne q hq)) where
  toFun tx := ⟨conjNormalize (stabRot e A B ((tx.1 : ℝ)) tx.2) (p tx.2),
    stabRot_conj_mem e hA hB hAB hBA hp _ _⟩
  continuous_toFun := by
    have hrot : Continuous fun tx : I × X => stabRot e A B ((tx.1 : ℝ)) tx.2 := by
      refine Continuous.add ?_ ?_
      · exact (Complex.continuous_ofReal.comp
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).smul
            continuous_const
      · exact (Complex.continuous_ofReal.comp
          (continuous_subtype_val.comp continuous_fst)).smul
            (continuous_const.matrix_mul (e.continuous_hom.comp continuous_snd))
    exact (continuous_conjNormalize hrot (p.continuous.comp continuous_snd)
      fun tx => trace_stabRot_conj_ne_zero e hA hB hAB hBA hp _ _).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    have h0 : stabRot e A B (((0 : I) : ℝ)) x = A := by
      rw [stabRot_def]
      norm_num
    show conjNormalize (stabRot e A B (((0 : I) : ℝ)) x) (p x) = A * p x * Aᴴ
    rw [conjNormalize_def, trace_stabRot_conj e hA hB hAB hBA hp, h0]
    norm_num
  map_one_left x := by
    apply Subtype.ext
    have h1 : stabRot e A B (((1 : I) : ℝ)) x = B * e.hom x := by
      rw [stabRot_def]
      norm_num
    have hBv : (B * e.hom x) * p x * (B * e.hom x)ᴴ = B * q x * Bᴴ := by
      rw [Matrix.conjTranspose_mul]
      calc B * e.hom x * p x * ((e.hom x)ᴴ * Bᴴ)
          = B * ((e.hom x * p x) * ((e.hom x)ᴴ * Bᴴ)) := by simp only [Matrix.mul_assoc]
        _ = B * (e.hom x * ((e.hom x)ᴴ * Bᴴ)) := by rw [e.hom_mul_right]
        _ = B * ((e.hom x * (e.hom x)ᴴ) * Bᴴ) := by simp only [Matrix.mul_assoc]
        _ = B * (q x * Bᴴ) := by rw [e.mul_conjTranspose]
        _ = B * q x * Bᴴ := by simp only [Matrix.mul_assoc]
    show conjNormalize (stabRot e A B (((1 : I) : ℝ)) x) (p x) = B * q x * Bᴴ
    rw [conjNormalize_def, trace_stabRot_conj e hA hB hAB hBA hp, h1, hBv]
    norm_num

theorem homotopic_cpEmbed_of_iso (e : BundleIso p q)
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (q x).trace = 1) :
    ((cpEmbed A hA).comp (classifyOne p hp)).Homotopic
      ((cpEmbed B hB).comp (classifyOne q hq)) :=
  ⟨stabHomotopy e hA hB hAB hBA hp hq⟩

/-- **The form the Euler class consumes**: isomorphic line bundles have
homotopic classifying maps after stabilisation along the **same** embedding.
Obtained by rotating twice, once along the isomorphism and once along the
identity. -/
theorem homotopic_cpEmbed_same (e : BundleIso p q)
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (q x).trace = 1) :
    ((cpEmbed A hA).comp (classifyOne p hp)).Homotopic
      ((cpEmbed A hA).comp (classifyOne q hq)) :=
  (homotopic_cpEmbed_of_iso e hA hB hAB hBA hp hq).trans
    (homotopic_cpEmbed_of_iso (BundleIso.refl q) hA hB hAB hBA hq hq).symm

end Stabilize

/-! ### A splitting of `ℂ^{N+1}` from an equivalence of index types -/

section Split

variable {ι κ ρ : Type} [Fintype ι] [Fintype κ] [Fintype ρ] [DecidableEq ρ]

/-- The isometry `ℂ^ι → ℂ^ρ` picking out the left summand of a splitting. -/
def sumInclLeft (eqv : ι ⊕ κ ≃ ρ) : Matrix ρ ι ℂ :=
  (1 : Matrix ρ ρ ℂ).submatrix id (fun i => eqv (Sum.inl i))

/-- The isometry `ℂ^κ → ℂ^ρ` picking out the right summand of a splitting. -/
def sumInclRight (eqv : ι ⊕ κ ≃ ρ) : Matrix ρ κ ℂ :=
  (1 : Matrix ρ ρ ℂ).submatrix id (fun k => eqv (Sum.inr k))

omit [Fintype ι] [Fintype κ] [Fintype ρ] [DecidableEq ρ] in
theorem sumInclLeft_injective (eqv : ι ⊕ κ ≃ ρ) :
    Function.Injective (fun i : ι => eqv (Sum.inl i)) :=
  fun _ _ h => Sum.inl_injective (eqv.injective h)

omit [Fintype ι] [Fintype κ] [Fintype ρ] [DecidableEq ρ] in
theorem sumInclRight_injective (eqv : ι ⊕ κ ≃ ρ) :
    Function.Injective (fun k : κ => eqv (Sum.inr k)) :=
  fun _ _ h => Sum.inr_injective (eqv.injective h)

omit [Fintype ι] [Fintype κ] in
theorem sumInclLeft_isometry [DecidableEq ι] (eqv : ι ⊕ κ ≃ ρ) :
    (sumInclLeft eqv)ᴴ * sumInclLeft eqv = 1 := by
  rw [sumInclLeft, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul (1 : Matrix ρ ρ ℂ) (1 : Matrix ρ ρ ℂ) _ id _ Function.bijective_id,
    Matrix.one_mul]
  exact Matrix.submatrix_one _ (sumInclLeft_injective eqv)

omit [Fintype ι] [Fintype κ] in
theorem sumInclRight_isometry [DecidableEq κ] (eqv : ι ⊕ κ ≃ ρ) :
    (sumInclRight eqv)ᴴ * sumInclRight eqv = 1 := by
  rw [sumInclRight, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul (1 : Matrix ρ ρ ℂ) (1 : Matrix ρ ρ ℂ) _ id _ Function.bijective_id,
    Matrix.one_mul]
  exact Matrix.submatrix_one _ (sumInclRight_injective eqv)

omit [Fintype ι] [Fintype κ] in
theorem sumInclLeft_conjTranspose_mul_right (eqv : ι ⊕ κ ≃ ρ) :
    (sumInclLeft eqv)ᴴ * sumInclRight eqv = 0 := by
  rw [sumInclLeft, sumInclRight, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul (1 : Matrix ρ ρ ℂ) (1 : Matrix ρ ρ ℂ) _ id _ Function.bijective_id,
    Matrix.one_mul]
  ext i k
  show (1 : Matrix ρ ρ ℂ) (eqv (Sum.inl i)) (eqv (Sum.inr k)) = 0
  rw [Matrix.one_apply_ne]
  intro h
  exact Sum.inl_ne_inr (eqv.injective h)

omit [Fintype ι] [Fintype κ] in
theorem sumInclRight_conjTranspose_mul_left (eqv : ι ⊕ κ ≃ ρ) :
    (sumInclRight eqv)ᴴ * sumInclLeft eqv = 0 := by
  rw [sumInclLeft, sumInclRight, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul (1 : Matrix ρ ρ ℂ) (1 : Matrix ρ ρ ℂ) _ id _ Function.bijective_id,
    Matrix.one_mul]
  ext k i
  show (1 : Matrix ρ ρ ℂ) (eqv (Sum.inr k)) (eqv (Sum.inl i)) = 0
  rw [Matrix.one_apply_ne]
  intro h
  exact Sum.inr_ne_inl (eqv.injective h)

end Split

end Bundle

end CharClass
end GroupApproximation
