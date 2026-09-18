import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFBlockIndex
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The universal UHF algebra `Q`: the block amplification `M_{m!} → M_{n!}`

Lane `TWWSch3d5a` (work order `WO-TWWSchafhauser-3d-5`, part (a)).

For `m ≤ n` and `d = n!/m!` the isometries `W_r : ℂ^{m!} → ℂ^{n!}`,
`W_r e_p = e_{p d + r}` (`r < d`), satisfy `W_r⋆ W_s = δ_{rs}` and
`∑_r W_r W_r⋆ = 1`.  The amplification `a ↦ ∑_r W_r a W_r⋆` (that is,
`a ⊗ 1_d`) is a unital `⋆`-homomorphism, contractive for the operator norm,
and compatible with towers `k ≤ m ≤ n`.  These are the connecting maps of the
inductive system `M_{1!} ⊂ M_{2!} ⊂ ⋯` defining `Q` (Glimm, Trans. AMS 95
(1960); Davidson, *C⋆-algebras by example*, Ch. III).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The building blocks are nonempty. -/
instance uhfFinNonempty (n : ℕ) : Nonempty (Fin n.factorial) :=
  ⟨⟨0, Nat.factorial_pos n⟩⟩

/-- The C⋆-algebra structure of a full matrix algebra (operator norm), used as a
local instance. -/
@[reducible] def uhfMatrixCStarAlgebra (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] :
    CStarAlgebra (Matrix W W ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable {m n : ℕ} (h : m ≤ n)

/-- The isometry `W_r : ℂ^{m!} → ℂ^{n!}`, `e_p ↦ e_{p d + r}`. -/
def uhfBlockIso (r : Fin (uhfBlockDim m n)) : Matrix (Fin n.factorial) (Fin m.factorial) ℂ :=
  Matrix.of fun i p ↦ if i = uhfBlockIndex h p r then 1 else 0

theorem uhfBlockIso_apply (r : Fin (uhfBlockDim m n)) (i : Fin n.factorial)
    (p : Fin m.factorial) : uhfBlockIso h r i p = if i = uhfBlockIndex h p r then 1 else 0 :=
  rfl

theorem uhfBlockIso_conjTranspose_apply (r : Fin (uhfBlockDim m n)) (p : Fin m.factorial)
    (i : Fin n.factorial) :
    (uhfBlockIso h r)ᴴ p i = if i = uhfBlockIndex h p r then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, uhfBlockIso_apply]
  split_ifs <;> simp

theorem mul_uhfBlockIso_apply {κ : Type*} (r : Fin (uhfBlockDim m n))
    (M : Matrix κ (Fin n.factorial) ℂ) (i : κ) (q : Fin m.factorial) :
    (M * uhfBlockIso h r) i q = M i (uhfBlockIndex h q r) := by
  have hz : ∀ j ≠ uhfBlockIndex h q r, M i j * uhfBlockIso h r j q = 0 := fun j hj ↦ by
    rw [uhfBlockIso_apply, if_neg hj, mul_zero]
  rw [Matrix.mul_apply, Fintype.sum_eq_single _ hz, uhfBlockIso_apply, if_pos rfl, mul_one]

theorem uhfBlockIso_conjTranspose_mul_apply {κ : Type*} (r : Fin (uhfBlockDim m n))
    (M : Matrix (Fin n.factorial) κ ℂ) (p : Fin m.factorial) (j : κ) :
    ((uhfBlockIso h r)ᴴ * M) p j = M (uhfBlockIndex h p r) j := by
  have hz : ∀ x ≠ uhfBlockIndex h p r, (uhfBlockIso h r)ᴴ p x * M x j = 0 := fun x hx ↦ by
    rw [uhfBlockIso_conjTranspose_apply, if_neg hx, zero_mul]
  rw [Matrix.mul_apply, Fintype.sum_eq_single _ hz, uhfBlockIso_conjTranspose_apply, if_pos rfl,
    one_mul]

theorem uhfBlockIso_mul_apply {κ : Type*} (r : Fin (uhfBlockDim m n))
    (M : Matrix (Fin m.factorial) κ ℂ) (i : Fin n.factorial) (j : κ) :
    (uhfBlockIso h r * M) i j =
      if uhfBlockFiber h i = r then M (uhfBlockProj h i) j else 0 := by
  have hz : ∀ p ≠ uhfBlockProj h i, uhfBlockIso h r i p * M p j = 0 := fun p hp ↦ by
    rw [uhfBlockIso_apply,
      if_neg (fun hi ↦ hp ((uhfBlockIndex_eq_iff h i p r).1 hi).1.symm), zero_mul]
  rw [Matrix.mul_apply, Fintype.sum_eq_single _ hz, uhfBlockIso_apply]
  by_cases hr : uhfBlockFiber h i = r
  · rw [if_pos hr, if_pos ((uhfBlockIndex_eq_iff h i (uhfBlockProj h i) r).2 ⟨rfl, hr⟩),
      one_mul]
  · rw [if_neg hr,
      if_neg (fun hi ↦ hr ((uhfBlockIndex_eq_iff h i (uhfBlockProj h i) r).1 hi).2), zero_mul]

theorem mul_uhfBlockIso_conjTranspose_apply {κ : Type*} (r : Fin (uhfBlockDim m n))
    (M : Matrix κ (Fin m.factorial) ℂ) (i : κ) (j : Fin n.factorial) :
    (M * (uhfBlockIso h r)ᴴ) i j =
      if uhfBlockFiber h j = r then M i (uhfBlockProj h j) else 0 := by
  have hz : ∀ p ≠ uhfBlockProj h j, M i p * (uhfBlockIso h r)ᴴ p j = 0 := fun p hp ↦ by
    rw [uhfBlockIso_conjTranspose_apply,
      if_neg (fun hj ↦ hp ((uhfBlockIndex_eq_iff h j p r).1 hj).1.symm), mul_zero]
  rw [Matrix.mul_apply, Fintype.sum_eq_single _ hz, uhfBlockIso_conjTranspose_apply]
  by_cases hr : uhfBlockFiber h j = r
  · rw [if_pos hr, if_pos ((uhfBlockIndex_eq_iff h j (uhfBlockProj h j) r).2 ⟨rfl, hr⟩),
      mul_one]
  · rw [if_neg hr,
      if_neg (fun hj ↦ hr ((uhfBlockIndex_eq_iff h j (uhfBlockProj h j) r).1 hj).2), mul_zero]

/-- `W_r⋆ W_s = δ_{rs}`. -/
theorem uhfBlockIso_conjTranspose_mul_iso (r s : Fin (uhfBlockDim m n)) :
    (uhfBlockIso h r)ᴴ * uhfBlockIso h s = if r = s then 1 else 0 := by
  ext p q
  rw [uhfBlockIso_conjTranspose_mul_apply, uhfBlockIso_apply]
  by_cases hrs : r = s
  · subst hrs
    rw [if_pos rfl, Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpq,
        if_neg (fun he : uhfBlockIndex h p r = uhfBlockIndex h q r ↦
          hpq (uhfBlockIndex_injective h he).1)]
  · rw [if_neg hrs, Matrix.zero_apply,
      if_neg (fun he : uhfBlockIndex h p r = uhfBlockIndex h q s ↦
        hrs (uhfBlockIndex_injective h he).2)]

/-- `∑_r W_r W_r⋆ = 1`. -/
theorem sum_uhfBlockIso_mul_conjTranspose :
    ∑ r, uhfBlockIso h r * (uhfBlockIso h r)ᴴ = 1 := by
  ext i j
  have hz : ∀ r ≠ uhfBlockFiber h i, (uhfBlockIso h r * (uhfBlockIso h r)ᴴ) i j = 0 :=
    fun r hr ↦ by rw [uhfBlockIso_mul_apply, if_neg (Ne.symm hr)]
  rw [Matrix.sum_apply, Fintype.sum_eq_single _ hz, uhfBlockIso_mul_apply, if_pos rfl,
    uhfBlockIso_conjTranspose_apply, uhfBlockIndex_proj_fiber, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij.symm]
  · rw [if_neg hij, if_neg (Ne.symm hij)]

/-- **The amplification** `a ↦ ∑_r W_r a W_r⋆ = a ⊗ 1_d`. -/
def uhfAmp (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    Matrix (Fin n.factorial) (Fin n.factorial) ℂ :=
  ∑ r, uhfBlockIso h r * a * (uhfBlockIso h r)ᴴ

theorem uhfAmp_def (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAmp h a = ∑ r, uhfBlockIso h r * a * (uhfBlockIso h r)ᴴ :=
  rfl

/-- The entries of `a ⊗ 1_d`. -/
theorem uhfAmp_apply (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ)
    (i j : Fin n.factorial) :
    uhfAmp h a i j =
      if uhfBlockFiber h i = uhfBlockFiber h j then a (uhfBlockProj h i) (uhfBlockProj h j)
        else 0 := by
  have hz : ∀ r ≠ uhfBlockFiber h j, (uhfBlockIso h r * a * (uhfBlockIso h r)ᴴ) i j = 0 :=
    fun r hr ↦ by rw [mul_uhfBlockIso_conjTranspose_apply, if_neg (Ne.symm hr)]
  rw [uhfAmp_def, Matrix.sum_apply, Fintype.sum_eq_single _ hz,
    mul_uhfBlockIso_conjTranspose_apply, if_pos rfl, uhfBlockIso_mul_apply]

theorem uhfAmp_mul_iso (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ)
    (s : Fin (uhfBlockDim m n)) : uhfAmp h a * uhfBlockIso h s = uhfBlockIso h s * a := by
  have hz : ∀ r ≠ s, uhfBlockIso h r * a * (uhfBlockIso h r)ᴴ * uhfBlockIso h s = 0 :=
    fun r hr ↦ by
      rw [Matrix.mul_assoc, uhfBlockIso_conjTranspose_mul_iso, if_neg hr, Matrix.mul_zero]
  rw [uhfAmp_def, Matrix.sum_mul, Fintype.sum_eq_single _ hz, Matrix.mul_assoc,
    uhfBlockIso_conjTranspose_mul_iso, if_pos rfl, Matrix.mul_one]

theorem uhfBlockIso_conjTranspose_mul_amp (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ)
    (s : Fin (uhfBlockDim m n)) :
    (uhfBlockIso h s)ᴴ * uhfAmp h a = a * (uhfBlockIso h s)ᴴ := by
  have hz : ∀ r ≠ s, (uhfBlockIso h s)ᴴ * (uhfBlockIso h r * a * (uhfBlockIso h r)ᴴ) = 0 :=
    fun r hr ↦ by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, uhfBlockIso_conjTranspose_mul_iso,
        if_neg (Ne.symm hr), Matrix.zero_mul, Matrix.zero_mul]
  rw [uhfAmp_def, Matrix.mul_sum, Fintype.sum_eq_single _ hz, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, uhfBlockIso_conjTranspose_mul_iso, if_pos rfl, Matrix.one_mul]

theorem uhfAmp_mul_iso_assoc {κ : Type*} (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ)
    (s : Fin (uhfBlockDim m n)) (M : Matrix (Fin m.factorial) κ ℂ) :
    uhfAmp h a * (uhfBlockIso h s * M) = uhfBlockIso h s * (a * M) := by
  rw [← Matrix.mul_assoc, uhfAmp_mul_iso, Matrix.mul_assoc]

theorem uhfBlockIso_conjTranspose_mul_amp_assoc {κ : Type*}
    (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) (s : Fin (uhfBlockDim m n))
    (M : Matrix (Fin n.factorial) κ ℂ) :
    (uhfBlockIso h s)ᴴ * (uhfAmp h a * M) = a * ((uhfBlockIso h s)ᴴ * M) := by
  rw [← Matrix.mul_assoc, uhfBlockIso_conjTranspose_mul_amp, Matrix.mul_assoc]
