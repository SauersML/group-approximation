import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabEntry
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.MatrixCorner

/-!
# Finite matrix blocks of `𝒦 ⊗ B`

For the spatial model `Stab B` of the stabilization `𝒦 ⊗ B`, we identify the corner
`P_n (𝒦 ⊗ B) P_n` with the matrix algebra `M_n(B)`:

* `matLift φ hmul hstar n : M_n(B) →⋆ₙₐ C`, `M ↦ Σ_{i,j<n} φ_{ij}(M_{ij})`, for any system of
  linear maps `φ_{ij} : B → C` satisfying the matrix unit relations
  `φ_{ij}(a) φ_{kl}(b) = δ_{jk} φ_{il}(ab)` and `φ_{ij}(a)^* = φ_{ji}(a^*)`;
* `matEmbed B n : M_n(B) →⋆ₙₐ B(ℓ²(ℕ, H_B))`, the case `φ_{ij}(b) = e_{ij} ⊗ π(b)`, which is
  injective and hence isometric;
* `entryMatrix n x ∈ M_n(B)`, the upper-left `n × n` block of `x ∈ 𝒦 ⊗ B`, with
  `matEmbed B n (entryMatrix n x) = P_n x P_n`, so `‖entryMatrix n x‖ ≤ ‖x‖`, and
  `entryMatrix n (a b) = entryMatrix n a · entryMatrix n b` when `a P_n = a`.

These norm estimates make the universal property of `𝒦 ⊗ B` (`Stab.lift`, in `StabLift`)
work: a matrix unit system extends continuously from the finite matrices (Cuntz, *A new look at
KK-theory*, K-Theory 1 (1987) 31--51, §1; Blackadar, *K-Theory for Operator Algebras*, 17.8).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-Stab, work orders WO-TWWKK-A1 and WO-TWWKK-A1x).
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

namespace Stab

variable {B : Type u} [NonUnitalCStarAlgebra B]

theorem sum_fin_fin_eq_range {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → ℕ → M) :
    ∑ i : Fin n, ∑ j : Fin n, F i j = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, F i j :=
  (Finset.sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (F i) n).trans
    (Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, F i j) n)

/-! ## Matrix unit systems and matrix algebras -/

section MatLift

variable {C : Type*} [NonUnitalCStarAlgebra C]

theorem lift_mul_sum_sum (φ : ℕ → ℕ → B →ₗ[ℂ] C)
    (hmul : ∀ i j k l a b, φ i j a * φ k l b = if j = k then φ i l (a * b) else 0)
    (n : ℕ) (i j : Fin n) (a : B) (N : Fin n → Fin n → B) :
    φ i j a * ∑ k : Fin n, ∑ l : Fin n, φ k l (N k l) = ∑ l : Fin n, φ i l (a * N j l) := by
  rw [Finset.mul_sum, Fintype.sum_eq_single j]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hmul, if_pos rfl]
  · intro k hk
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hmul, if_neg (fun h : (j : ℕ) = k => hk (Fin.ext h).symm)]

theorem lift_sum_sum_mul (φ : ℕ → ℕ → B →ₗ[ℂ] C)
    (hmul : ∀ i j k l a b, φ i j a * φ k l b = if j = k then φ i l (a * b) else 0)
    (n : ℕ) (M N : Fin n → Fin n → B) :
    (∑ i : Fin n, ∑ j : Fin n, φ i j (M i j)) * ∑ k : Fin n, ∑ l : Fin n, φ k l (N k l) =
      ∑ i : Fin n, ∑ l : Fin n, φ i l (∑ j : Fin n, M i j * N j l) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc (∑ j : Fin n, φ i j (M i j)) * ∑ k : Fin n, ∑ l : Fin n, φ k l (N k l)
      = ∑ j : Fin n, ∑ l : Fin n, φ i l (M i j * N j l) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => lift_mul_sum_sum φ hmul n i j (M i j) N
    _ = ∑ l : Fin n, ∑ j : Fin n, φ i l (M i j * N j l) := Finset.sum_comm
    _ = ∑ l : Fin n, φ i l (∑ j : Fin n, M i j * N j l) :=
        Finset.sum_congr rfl fun l _ =>
          (map_sum (φ i l) (fun j => M i j * N j l) Finset.univ).symm

/-- **A matrix unit system induces a `⋆`-homomorphism on `M_n(B)`**: `M ↦ Σ φ_{ij}(M_{ij})`. -/
def matLift (φ : ℕ → ℕ → B →ₗ[ℂ] C)
    (hmul : ∀ i j k l a b, φ i j a * φ k l b = if j = k then φ i l (a * b) else 0)
    (hstar : ∀ i j a, star (φ i j a) = φ j i (star a)) (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) B →⋆ₙₐ[ℂ] C where
  toFun M := ∑ i : Fin n, ∑ j : Fin n, φ i j (M i j)
  map_smul' c M := by
    change ∑ i : Fin n, ∑ j : Fin n, φ i j (c • M i j) =
      c • ∑ i : Fin n, ∑ j : Fin n, φ i j (M i j)
    simp only [map_smul, Finset.smul_sum]
  map_zero' := by
    change ∑ i : Fin n, ∑ j : Fin n, φ i j (0 : B) = 0
    simp only [map_zero, Finset.sum_const_zero]
  map_add' M N := by
    change ∑ i : Fin n, ∑ j : Fin n, φ i j (M i j + N i j) =
      ∑ i : Fin n, ∑ j : Fin n, φ i j (M i j) + ∑ i : Fin n, ∑ j : Fin n, φ i j (N i j)
    simp only [map_add, Finset.sum_add_distrib]
  map_mul' M N := by
    change ∑ i : Fin n, ∑ l : Fin n, φ i l (∑ j : Fin n, M i j * N j l) =
      (∑ i : Fin n, ∑ j : Fin n, φ i j (M i j)) * ∑ k : Fin n, ∑ l : Fin n, φ k l (N k l)
    exact (lift_sum_sum_mul φ hmul n (fun i j => M i j) (fun i j => N i j)).symm
  map_star' M := by
    change ∑ i : Fin n, ∑ j : Fin n, φ i j (star (M j i)) =
      star (∑ i : Fin n, ∑ j : Fin n, φ i j (M i j))
    simp only [star_sum, hstar]
    exact Finset.sum_comm

theorem matLift_apply (φ : ℕ → ℕ → B →ₗ[ℂ] C)
    (hmul : ∀ i j k l a b, φ i j a * φ k l b = if j = k then φ i l (a * b) else 0)
    (hstar : ∀ i j a, star (φ i j a) = φ j i (star a)) (n : ℕ)
    (M : CStarMatrix (Fin n) (Fin n) B) :
    matLift φ hmul hstar n M = ∑ i : Fin n, ∑ j : Fin n, φ i j (M i j) :=
  rfl

theorem norm_matLift_le (φ : ℕ → ℕ → B →ₗ[ℂ] C)
    (hmul : ∀ i j k l a b, φ i j a * φ k l b = if j = k then φ i l (a * b) else 0)
    (hstar : ∀ i j a, star (φ i j a) = φ j i (star a)) (n : ℕ)
    (M : CStarMatrix (Fin n) (Fin n) B) : ‖matLift φ hmul hstar n M‖ ≤ ‖M‖ :=
  NonUnitalStarAlgHom.norm_apply_le (matLift φ hmul hstar n) M

end MatLift

/-! ## The spatial matrix units `e_{ij} ⊗ π(b)` -/

variable (B) in
/-- `b ↦ e_{ij} ⊗ π(b)`, as a linear map `B → B(ℓ²(ℕ, H_B))`. -/
def matUnitRep (i j : ℕ) : B →ₗ[ℂ] Ambient B where
  toFun b := matUnit B i j (rep B b)
  map_add' a b := by
    change matUnit B i j (rep B (a + b)) = matUnit B i j (rep B a) + matUnit B i j (rep B b)
    rw [map_add, matUnit_add]
  map_smul' c b := by
    change matUnit B i j (rep B (c • b)) = c • matUnit B i j (rep B b)
    rw [map_smul, matUnit_smul]

theorem matUnitRep_apply (i j : ℕ) (b : B) : matUnitRep B i j b = matUnit B i j (rep B b) :=
  rfl

theorem matUnitRep_mul (i j k l : ℕ) (a b : B) :
    matUnitRep B i j a * matUnitRep B k l b = if j = k then matUnitRep B i l (a * b) else 0 := by
  change matUnit B i j (rep B a) * matUnit B k l (rep B b) =
    if j = k then matUnit B i l (rep B (a * b)) else 0
  rw [matUnit_mul_matUnit, map_mul]

theorem matUnitRep_star (i j : ℕ) (a : B) :
    star (matUnitRep B i j a) = matUnitRep B j i (star a) := by
  change star (matUnit B i j (rep B a)) = matUnit B j i (rep B (star a))
  rw [map_star, star_matUnit]

variable (B) in
/-- **The embedding `M_n(B) → B(ℓ²(ℕ, H_B))`** onto the upper-left `n × n` block of `𝒦 ⊗ B`. -/
def matEmbed (n : ℕ) : CStarMatrix (Fin n) (Fin n) B →⋆ₙₐ[ℂ] Ambient B :=
  matLift (matUnitRep B) matUnitRep_mul matUnitRep_star n

theorem matEmbed_apply (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) B) :
    matEmbed B n M = ∑ i : Fin n, ∑ j : Fin n, matUnit B i j (rep B (M i j)) :=
  rfl

theorem compress_matEmbed (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) B) (k l : Fin n) :
    compress B k l (matEmbed B n M) = rep B (M k l) := by
  have h1 : ∀ i j : Fin n, compress B k l (matUnit B i j (rep B (M i j))) =
      if k = i then (if l = j then rep B (M i j) else 0) else 0 := by
    intro i j
    rw [compress_matUnit]
    by_cases hi : k = i
    · by_cases hj : l = j
      · rw [if_pos (show (k : ℕ) = i ∧ (l : ℕ) = j from ⟨congrArg Fin.val hi, congrArg Fin.val hj⟩),
          if_pos hi, if_pos hj]
      · rw [if_neg (fun h : (k : ℕ) = i ∧ (l : ℕ) = j => hj (Fin.ext h.2)), if_pos hi, if_neg hj]
    · rw [if_neg (fun h : (k : ℕ) = i ∧ (l : ℕ) = j => hi (Fin.ext h.1)), if_neg hi]
  rw [matEmbed_apply]
  simp only [map_sum, h1, Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq]

theorem matEmbed_injective (n : ℕ) : Function.Injective (matEmbed B n) := fun M N h =>
  CStarMatrix.ext fun i j => rep_injective B <| by
    rw [← compress_matEmbed n M i j, ← compress_matEmbed n N i j, h]

/-- The embedding `M_n(B) → B(ℓ²(ℕ, H_B))` is isometric. -/
theorem norm_matEmbed (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) B) :
    ‖matEmbed B n M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map (matEmbed B n) (matEmbed_injective n) M

/-! ## The matrix units `e_{ij} ⊗ b` of `𝒦 ⊗ B` -/

/-- `b ↦ e_{ij} ⊗ b`, as a linear map `B → 𝒦 ⊗ B`. -/
def singleₗ (i j : ℕ) : B →ₗ[ℂ] Stab B where
  toFun := single i j
  map_add' a b := Subtype.ext <| by
    change matUnit B i j (rep B (a + b)) = matUnit B i j (rep B a) + matUnit B i j (rep B b)
    rw [map_add, matUnit_add]
  map_smul' c b := Subtype.ext <| by
    change matUnit B i j (rep B (c • b)) = c • matUnit B i j (rep B b)
    rw [map_smul, matUnit_smul]

theorem singleₗ_apply (i j : ℕ) (b : B) : singleₗ i j b = single i j b :=
  rfl

theorem single_zero (i j : ℕ) : single i j (0 : B) = 0 :=
  Subtype.ext <| by
    change matUnit B i j (rep B 0) = 0
    rw [map_zero, matUnit_zero]

theorem single_add (i j : ℕ) (a b : B) : single i j (a + b) = single i j a + single i j b :=
  Subtype.ext <| by
    change matUnit B i j (rep B (a + b)) = matUnit B i j (rep B a) + matUnit B i j (rep B b)
    rw [map_add, matUnit_add]

/-- **Matrix unit relations in `𝒦 ⊗ B`**: `(e_{ij} ⊗ a)(e_{kl} ⊗ b) = δ_{jk} e_{il} ⊗ ab`. -/
theorem single_mul_single (i j k l : ℕ) (a b : B) :
    single i j a * single k l b = if j = k then single i l (a * b) else 0 := by
  by_cases h : j = k
  · rw [if_pos h]
    refine Subtype.ext ?_
    change matUnit B i j (rep B a) * matUnit B k l (rep B b) = matUnit B i l (rep B (a * b))
    rw [matUnit_mul_matUnit, if_pos h, map_mul]
  · rw [if_neg h]
    refine Subtype.ext ?_
    change matUnit B i j (rep B a) * matUnit B k l (rep B b) = 0
    rw [matUnit_mul_of_ne h]

theorem star_single (i j : ℕ) (a : B) : star (single i j a) = single j i (star a) :=
  Subtype.ext <| by
    change star (matUnit B i j (rep B a)) = matUnit B j i (rep B (star a))
    rw [map_star, star_matUnit]

theorem single_smul (i j : ℕ) (c : ℂ) (b : B) : single i j (c • b) = c • single i j b :=
  Subtype.ext <| by
    change matUnit B i j (rep B (c • b)) = c • matUnit B i j (rep B b)
    rw [map_smul, matUnit_smul]

variable (B) in
/-- **The block embedding `M_n(B) → 𝒦 ⊗ B`**, `M ↦ Σ_{i,j<n} e_{ij} ⊗ M_{ij}`. -/
def ofMat (n : ℕ) : CStarMatrix (Fin n) (Fin n) B →⋆ₙₐ[ℂ] Stab B :=
  matLift (fun i j => singleₗ i j) (fun i j k l a b => single_mul_single i j k l a b)
    (fun i j a => star_single i j a) n

theorem ofMat_apply (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) B) :
    ofMat B n M = ∑ i : Fin n, ∑ j : Fin n, single i j (M i j) :=
  rfl

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → Stab B) :
    ((∑ i ∈ s, f i : Stab B) : Ambient B) = ∑ i ∈ s, (f i : Ambient B) :=
  AddSubmonoidClass.coe_finsetSum f s

/-! ## The upper-left blocks of an element of `𝒦 ⊗ B` -/

/-- The upper-left `n × n` block `(x_{ij})_{i,j<n} ∈ M_n(B)` of `x ∈ 𝒦 ⊗ B`. -/
def entryMatrix (n : ℕ) (x : Stab B) : CStarMatrix (Fin n) (Fin n) B :=
  CStarMatrix.ofMatrix (Matrix.of fun i j : Fin n => entry i j x)

theorem entryMatrix_apply (n : ℕ) (x : Stab B) (i j : Fin n) :
    entryMatrix n x i j = entry i j x :=
  rfl

theorem entryMatrix_star (n : ℕ) (x : Stab B) :
    entryMatrix n (star x) = star (entryMatrix n x) :=
  CStarMatrix.ext fun i j => entry_star (B := B) i j x

theorem matEmbed_entryMatrix (n : ℕ) (x : Stab B) :
    matEmbed B n (entryMatrix n x) = trunc B n * (x : Ambient B) * trunc B n := by
  rw [matEmbed_apply, trunc_mul_mul_trunc_eq_sum]
  refine (sum_fin_fin_eq_range n fun i j => matUnit B i j (rep B (entry i j x))).trans ?_
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    congrArg (matUnit B i j) (rep_entry i j x)

/-- The upper-left blocks are contractive: `‖(x_{ij})_{i,j<n}‖ = ‖P_n x P_n‖ ≤ ‖x‖`. -/
theorem norm_entryMatrix_le (n : ℕ) (x : Stab B) : ‖entryMatrix n x‖ ≤ ‖x‖ :=
  calc ‖entryMatrix n x‖ = ‖matEmbed B n (entryMatrix n x)‖ := (norm_matEmbed n _).symm
    _ = ‖trunc B n * (x : Ambient B) * trunc B n‖ := by rw [matEmbed_entryMatrix]
    _ ≤ ‖(x : Ambient B)‖ := norm_trunc_mul_mul_trunc_le n _
    _ = ‖x‖ := rfl

/-- The upper-left block of a product `a b` with `a P_n = a` is the product of the blocks. -/
theorem entryMatrix_mul_of {n : ℕ} {a : Stab B} (ha : (a : Ambient B) * trunc B n = a)
    (b : Stab B) : entryMatrix n (a * b) = entryMatrix n a * entryMatrix n b :=
  CStarMatrix.ext fun i j => rep_injective B <| by
    change rep B (entry i j (a * b)) = rep B (∑ k : Fin n, entry i k a * entry k j b)
    rw [rep_entry, map_sum]
    refine (compress_mul_of_mul_trunc ha (b : Ambient B) i j).trans ?_
    refine (Fin.sum_univ_eq_sum_range
      (fun k => compress B i k (a : Ambient B) * compress B k j (b : Ambient B)) n).symm.trans ?_
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, rep_entry, rep_entry]
