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
      if_neg (fun hi : i = uhfBlockIndex h p r ↦
        hp ((uhfBlockIndex_eq_iff h i p r).1 hi).1.symm), zero_mul]
  rw [Matrix.mul_apply, Fintype.sum_eq_single _ hz, uhfBlockIso_apply]
  by_cases hr : uhfBlockFiber h i = r
  · rw [if_pos hr, if_pos ((uhfBlockIndex_eq_iff h i (uhfBlockProj h i) r).2 ⟨rfl, hr⟩),
      one_mul]
  · rw [if_neg hr,
      if_neg (fun hi : i = uhfBlockIndex h (uhfBlockProj h i) r ↦
        hr ((uhfBlockIndex_eq_iff h i (uhfBlockProj h i) r).1 hi).2), zero_mul]

theorem mul_uhfBlockIso_conjTranspose_apply {κ : Type*} (r : Fin (uhfBlockDim m n))
    (M : Matrix κ (Fin m.factorial) ℂ) (i : κ) (j : Fin n.factorial) :
    (M * (uhfBlockIso h r)ᴴ) i j =
      if uhfBlockFiber h j = r then M i (uhfBlockProj h j) else 0 := by
  have hz : ∀ p ≠ uhfBlockProj h j, M i p * (uhfBlockIso h r)ᴴ p j = 0 := fun p hp ↦ by
    rw [uhfBlockIso_conjTranspose_apply,
      if_neg (fun hj : j = uhfBlockIndex h p r ↦
        hp ((uhfBlockIndex_eq_iff h j p r).1 hj).1.symm), mul_zero]
  rw [Matrix.mul_apply, Fintype.sum_eq_single _ hz, uhfBlockIso_conjTranspose_apply]
  by_cases hr : uhfBlockFiber h j = r
  · rw [if_pos hr, if_pos ((uhfBlockIndex_eq_iff h j (uhfBlockProj h j) r).2 ⟨rfl, hr⟩),
      mul_one]
  · rw [if_neg hr,
      if_neg (fun hj : j = uhfBlockIndex h (uhfBlockProj h j) r ↦
        hr ((uhfBlockIndex_eq_iff h j (uhfBlockProj h j) r).1 hj).2), mul_zero]

/-- `W_r⋆ W_s = δ_{rs}`. -/
theorem uhfBlockIso_conjTranspose_mul_iso (r s : Fin (uhfBlockDim m n)) :
    (uhfBlockIso h r)ᴴ * uhfBlockIso h s = if r = s then 1 else 0 := by
  ext p q
  rw [uhfBlockIso_conjTranspose_mul_apply, uhfBlockIso_apply]
  by_cases hrs : r = s
  · rw [if_pos hrs, Matrix.one_apply, ← hrs]
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

theorem uhfAmp_mul (a b : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAmp h (a * b) = uhfAmp h a * uhfAmp h b := by
  rw [uhfAmp_def h b, Matrix.mul_sum, uhfAmp_def h (a * b)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Matrix.mul_assoc (uhfBlockIso h r) b, uhfAmp_mul_iso_assoc,
    Matrix.mul_assoc (uhfBlockIso h r) (a * b), Matrix.mul_assoc a b]

theorem uhfAmp_one : uhfAmp h (1 : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) = 1 := by
  rw [uhfAmp_def]
  simp only [Matrix.mul_one]
  exact sum_uhfBlockIso_mul_conjTranspose h

theorem uhfAmp_zero : uhfAmp h (0 : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) = 0 := by
  rw [uhfAmp_def]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Finset.sum_const_zero]

theorem uhfAmp_add (a b : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAmp h (a + b) = uhfAmp h a + uhfAmp h b := by
  rw [uhfAmp_def h (a + b), uhfAmp_def h a, uhfAmp_def h b, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Matrix.mul_add, Matrix.add_mul]

theorem uhfAmp_smul (c : ℂ) (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAmp h (c • a) = c • uhfAmp h a := by
  rw [uhfAmp_def h (c • a), uhfAmp_def h a, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem uhfAmp_star (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAmp h (star a) = star (uhfAmp h a) := by
  rw [uhfAmp_def h (star a), uhfAmp_def h a, star_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Matrix.star_eq_conjTranspose a,
    Matrix.star_eq_conjTranspose (uhfBlockIso h r * a * (uhfBlockIso h r)ᴴ),
    Matrix.conjTranspose_mul (uhfBlockIso h r * a) (uhfBlockIso h r)ᴴ,
    Matrix.conjTranspose_mul (uhfBlockIso h r) a, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc (uhfBlockIso h r) aᴴ]

/-- **The connecting map** `M_{m!} → M_{n!}`, `a ↦ a ⊗ 1_d`, as a unital
`⋆`-homomorphism. -/
def uhfAmpHom : Matrix (Fin m.factorial) (Fin m.factorial) ℂ →⋆ₐ[ℂ]
    Matrix (Fin n.factorial) (Fin n.factorial) ℂ where
  toFun := uhfAmp h
  map_one' := uhfAmp_one h
  map_mul' := uhfAmp_mul h
  map_zero' := uhfAmp_zero h
  map_add' := uhfAmp_add h
  commutes' c := by
    show uhfAmp h (algebraMap ℂ (Matrix (Fin m.factorial) (Fin m.factorial) ℂ) c) =
      algebraMap ℂ (Matrix (Fin n.factorial) (Fin n.factorial) ℂ) c
    rw [Algebra.algebraMap_eq_smul_one c, Algebra.algebraMap_eq_smul_one c, uhfAmp_smul,
      uhfAmp_one]
  map_star' := uhfAmp_star h

theorem uhfAmpHom_apply (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAmpHom h a = uhfAmp h a :=
  rfl

/-- The connecting maps compose along a tower `k ≤ m ≤ n`. -/
theorem uhfAmp_uhfAmp {k : ℕ} (hkm : k ≤ m) (hmn : m ≤ n)
    (b : Matrix (Fin k.factorial) (Fin k.factorial) ℂ) :
    uhfAmp hmn (uhfAmp hkm b) = uhfAmp (Nat.le_trans hkm hmn) b := by
  ext i j
  rw [uhfAmp_apply hmn, uhfAmp_apply hkm, uhfAmp_apply (Nat.le_trans hkm hmn),
    uhfBlockProj_proj hkm hmn i, uhfBlockProj_proj hkm hmn j]
  by_cases h1 : uhfBlockFiber hmn i = uhfBlockFiber hmn j
  · by_cases h2 : uhfBlockFiber hkm (uhfBlockProj hmn i) = uhfBlockFiber hkm (uhfBlockProj hmn j)
    · rw [if_pos h1, if_pos h2, if_pos ((uhfBlockFiber_eq_iff hkm hmn i j).2 ⟨h1, h2⟩)]
    · rw [if_pos h1, if_neg h2,
        if_neg (fun h3 : uhfBlockFiber (Nat.le_trans hkm hmn) i =
            uhfBlockFiber (Nat.le_trans hkm hmn) j ↦
          h2 ((uhfBlockFiber_eq_iff hkm hmn i j).1 h3).2)]
  · rw [if_neg h1,
      if_neg (fun h3 : uhfBlockFiber (Nat.le_trans hkm hmn) i =
          uhfBlockFiber (Nat.le_trans hkm hmn) j ↦
        h1 ((uhfBlockFiber_eq_iff hkm hmn i j).1 h3).1)]

/-- The amplification of the identity level is the identity. -/
theorem uhfAmp_self (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    uhfAmp (le_refl m) a = a := by
  ext i j
  rw [uhfAmp_apply]
  have hd : uhfBlockDim m m = 1 := by
    unfold uhfBlockDim
    exact Nat.div_self (Nat.factorial_pos m)
  have hfib : ∀ x : Fin m.factorial,
      uhfBlockFiber (le_refl m) x = ⟨0, uhfBlockDim_pos (le_refl m)⟩ :=
    fun x ↦ Fin.ext (by
      show x.1 % uhfBlockDim m m = 0
      rw [hd, Nat.mod_one])
  have hproj : ∀ x : Fin m.factorial, uhfBlockProj (le_refl m) x = x :=
    fun x ↦ Fin.ext (by
      show x.1 / uhfBlockDim m m = x.1
      rw [hd, Nat.div_one])
  rw [if_pos ((hfib i).trans (hfib j).symm), hproj, hproj]

section Norm

attribute [local instance] uhfMatrixCStarAlgebra

/-- The connecting maps are contractive in the operator norm (indeed isometric). -/
theorem norm_uhfAmp_le (a : Matrix (Fin m.factorial) (Fin m.factorial) ℂ) :
    ‖uhfAmp h a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (uhfAmpHom h) a

end Norm

end

end GroupApproximation.Full.TWWSchafhauser
