import GroupApproximation.CharClass.BundleBlockIncl
import GroupApproximation.CharClass.ProjectiveSpaceHyperplane

/-!
# Complex vector bundles in the projection model, XV: coordinate embeddings

`cpEmbed` turns a linear isometric embedding into a map of projective spaces.
This file supplies what a consumer needs to *identify* such a map: how they
compose, when two of them are homotopic, and the fact that the hyperplane
inclusion `ℂP^d ↪ ℂP^{d+1}` is one of them.

The isometries that occur in practice are all **coordinate embeddings**: an
injection `f : ι → ρ` of index sets gives `coordIncl f`, the matrix `[s = f i]`,
and every such matrix is an isometry.  Composition of coordinate embeddings is
composition of index maps (`coordIncl_mul_coordIncl`), their ranges are
orthogonal exactly when the index maps have disjoint images
(`coordIncl_conjTranspose_mul_of_disjoint`), and the conjugation
`z ↦ A z Aᴴ` spreads `z` over the image of `f` and is zero off it.

Two consequences are what the Euler class needs.  `cpEmbed_shiftMat` says the
hyperplane inclusion of `ProjectiveSpaceHyperplane` **is** a `cpEmbed`, for the
shift `Fin.succ`, so its effect on cohomology is available to any argument
phrased over `cpEmbed`.  `homotopic_cpEmbed_of_orthogonal` says two isometries
with orthogonal ranges give homotopic maps, which is the rotation of
`BundleStabilize` specialized at the tautological bundle and the identity
isomorphism -- note the orthogonality hypothesis is genuinely needed here; two
arbitrary isometries into the same space are also homotopic, but that is the
connectivity of a Stiefel manifold and is not proved here.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### Coordinate embeddings -/

section Coord

/-- The matrix of a coordinate embedding: `1` where `s = f i`, `0` elsewhere. -/
def coordIncl {ι ρ : Type} [DecidableEq ρ] (f : ι → ρ) : Matrix ρ ι ℂ :=
  Matrix.of fun s i => if s = f i then (1 : ℂ) else 0

theorem coordIncl_apply {ι ρ : Type} [DecidableEq ρ] (f : ι → ρ) (s : ρ) (i : ι) :
    coordIncl f s i = if s = f i then (1 : ℂ) else 0 := rfl

theorem coordIncl_isometry {ι ρ : Type} [Fintype ρ] [DecidableEq ρ] [DecidableEq ι]
    {f : ι → ρ} (hf : Function.Injective f) :
    (coordIncl f)ᴴ * coordIncl f = (1 : Matrix ι ι ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ s : ρ, ((coordIncl f)ᴴ) i s * coordIncl f s j
      = if s = f i then (if s = f j then (1 : ℂ) else 0) else 0 := by
    intro s
    rw [Matrix.conjTranspose_apply, coordIncl_apply, coordIncl_apply]
    by_cases h : s = f i
    · rw [if_pos h, if_pos h]
      simp
    · rw [if_neg h, if_neg h]
      simp
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (fun hc => h (hf hc)), if_neg h]

theorem coordIncl_mul_apply {ι ρ : Type} [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    {f : ι → ρ} (hf : Function.Injective f) (z : Matrix ι ι ℂ) (i l : ι) :
    (coordIncl f * z) (f i) l = z i l := by
  rw [Matrix.mul_apply]
  have hterm : ∀ m : ι, coordIncl f (f i) m * z m l = if i = m then z m l else 0 := by
    intro m
    rw [coordIncl_apply]
    by_cases h : i = m
    · subst h
      simp
    · rw [if_neg (fun hc => h (hf hc)), if_neg h, zero_mul]
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  simp

theorem coordIncl_mul_apply_of_ne {ι ρ : Type} [Fintype ι] [DecidableEq ρ]
    {f : ι → ρ} {s : ρ} (hs : ∀ i, s ≠ f i) (z : Matrix ι ι ℂ) (l : ι) :
    (coordIncl f * z) s l = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [coordIncl_apply, if_neg (hs m), zero_mul]

/-- **The conjugate carries the entries of `z` onto the image of `f`.** -/
theorem coordIncl_conj_apply {ι ρ : Type} [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    {f : ι → ρ} (hf : Function.Injective f) (z : Matrix ι ι ℂ) (i j : ι) :
    (coordIncl f * z * (coordIncl f)ᴴ) (f i) (f j) = z i j := by
  rw [Matrix.mul_apply]
  have hterm : ∀ l : ι, (coordIncl f * z) (f i) l * ((coordIncl f)ᴴ) l (f j)
      = if j = l then z i l else 0 := by
    intro l
    rw [coordIncl_mul_apply hf, Matrix.conjTranspose_apply, coordIncl_apply]
    by_cases h : j = l
    · subst h
      simp
    · rw [if_neg (fun hc => h (hf hc)), if_neg h, star_zero, mul_zero]
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  simp

/-- **The conjugate vanishes off the image of `f`**, in the row index. -/
theorem coordIncl_conj_apply_row {ι ρ : Type} [Fintype ι] [DecidableEq ρ]
    {f : ι → ρ} {s : ρ} (hs : ∀ i, s ≠ f i) (z : Matrix ι ι ℂ) (t : ρ) :
    (coordIncl f * z * (coordIncl f)ᴴ) s t = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [coordIncl_mul_apply_of_ne hs, zero_mul]

/-- **The conjugate vanishes off the image of `f`**, in the column index. -/
theorem coordIncl_conj_apply_col {ι ρ : Type} [Fintype ι] [DecidableEq ρ]
    {f : ι → ρ} {t : ρ} (ht : ∀ j, t ≠ f j) (z : Matrix ι ι ℂ) (s : ρ) :
    (coordIncl f * z * (coordIncl f)ᴴ) s t = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.conjTranspose_apply, coordIncl_apply, if_neg (ht l), star_zero, mul_zero]

/-- **Disjoint images give orthogonal ranges.** -/
theorem coordIncl_conjTranspose_mul_of_disjoint {ι κ ρ : Type} [Fintype ρ] [DecidableEq ρ]
    {f : ι → ρ} {g : κ → ρ} (h : ∀ i k, f i ≠ g k) :
    (coordIncl f)ᴴ * coordIncl g = 0 := by
  ext i k
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Matrix.conjTranspose_apply, coordIncl_apply, coordIncl_apply]
  by_cases hs : s = f i
  · subst hs
    rw [if_neg (h i k)]
    simp
  · rw [if_neg hs]
    simp

/-- **Composing coordinate embeddings composes the index maps.** -/
theorem coordIncl_mul_coordIncl {ι κ ρ : Type} [Fintype κ] [DecidableEq ρ] [DecidableEq κ]
    (f : ι → κ) (g : κ → ρ) : coordIncl g * coordIncl f = coordIncl (g ∘ f) := by
  ext s i
  rw [Matrix.mul_apply, coordIncl_apply]
  have hterm : ∀ m : κ, coordIncl g s m * coordIncl f m i
      = if m = f i then (if s = g m then (1 : ℂ) else 0) else 0 := by
    intro m
    rw [coordIncl_apply, coordIncl_apply]
    by_cases h : m = f i <;> simp [h]
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rfl

/-- The block isometry of `BundleStabilize` is a coordinate embedding. -/
theorem sumInclLeft_eq_coordIncl {ι κ ρ : Type} [Fintype ι] [Fintype κ] [DecidableEq ρ]
    (eqv : ι ⊕ κ ≃ ρ) : sumInclLeft eqv = coordIncl (fun i => eqv (Sum.inl i)) := by
  ext s i
  rw [sumInclLeft_apply, coordIncl_apply]

end Coord

/-! ### Composition of `cpEmbed` -/

section Comp

/-- The composite of two isometries is an isometry. -/
theorem isometry_mul {d e N : ℕ} {A : Matrix (Fin (e + 1)) (Fin (d + 1)) ℂ}
    {B : Matrix (Fin (N + 1)) (Fin (e + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (B * A)ᴴ * (B * A) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc Aᴴ * Bᴴ * (B * A) = Aᴴ * ((Bᴴ * B) * A) := by simp only [Matrix.mul_assoc]
    _ = Aᴴ * A := by rw [hB, Matrix.one_mul]
    _ = 1 := hA

/-- **`cpEmbed` is functorial in the isometry.** -/
theorem cpEmbed_comp {d e N : ℕ} {A : Matrix (Fin (e + 1)) (Fin (d + 1)) ℂ}
    {B : Matrix (Fin (N + 1)) (Fin (e + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (cpEmbed B hB).comp (cpEmbed A hA) = cpEmbed (B * A) (isometry_mul hA hB) := by
  refine ContinuousMap.ext fun z => Subtype.ext ?_
  show B * (A * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Aᴴ) * Bᴴ
    = B * A * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (B * A)ᴴ
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **Isometries with orthogonal ranges give homotopic maps.**  This is the
rotation of `BundleStabilize` at the tautological bundle and the identity
isomorphism; the orthogonality hypothesis is genuinely needed. -/
theorem homotopic_cpEmbed_of_orthogonal {d N : ℕ}
    {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) :
    (cpEmbed A hA).Homotopic (cpEmbed B hB) := by
  have h := homotopic_cpEmbed_of_iso (BundleIso.refl (cpTaut d)) hA hB hAB hBA
    (trace_cpTaut d) (trace_cpTaut d)
  rwa [classifyOne_cpTaut, ContinuousMap.comp_id, ContinuousMap.comp_id] at h

end Comp

/-! ### The hyperplane inclusion is a `cpEmbed` -/

section Hyperplane

/-- The shift `Fin (d+1) → Fin (d+2)`, as an isometry. -/
def shiftMat (d : ℕ) : Matrix (Fin (d + 2)) (Fin (d + 1)) ℂ :=
  coordIncl (Fin.succ : Fin (d + 1) → Fin (d + 2))

theorem shiftMat_def (d : ℕ) :
    shiftMat d = coordIncl (Fin.succ : Fin (d + 1) → Fin (d + 2)) := rfl

theorem shiftMat_isometry (d : ℕ) : (shiftMat d)ᴴ * shiftMat d = 1 :=
  coordIncl_isometry (Fin.succ_injective (d + 1))

/-- **The hyperplane inclusion is the `cpEmbed` of the shift**, entrywise. -/
theorem cpEmbed_shiftMat_coe (d : ℕ) (z : CP d) :
    (cpEmbed (shiftMat d) (shiftMat_isometry d) z
        : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ) = CPn.inclMat z := by
  rw [cpEmbed_apply, shiftMat_def]
  ext a b
  refine Fin.cases ?_ ?_ a
  · rw [CPn.inclMat_zero_row]
    exact coordIncl_conj_apply_row (fun i => (Fin.succ_ne_zero i).symm) _ b
  · intro i
    refine Fin.cases ?_ ?_ b
    · rw [CPn.inclMat_succ_zero]
      exact coordIncl_conj_apply_col (fun j => (Fin.succ_ne_zero j).symm) _ _
    · intro j
      rw [CPn.inclMat_succ_succ]
      exact coordIncl_conj_apply (Fin.succ_injective (d + 1)) _ i j

/-- **The hyperplane inclusion is a `cpEmbed`.** -/
theorem cpEmbed_shiftMat (d : ℕ) :
    cpEmbed (shiftMat d) (shiftMat_isometry d)
      = (⟨CPn.incl, CPn.continuous_incl⟩ : C(CP d, CP (d + 1))) :=
  ContinuousMap.ext fun z => Subtype.ext (cpEmbed_shiftMat_coe d z)

end Hyperplane

end Bundle

end CharClass
end GroupApproximation
