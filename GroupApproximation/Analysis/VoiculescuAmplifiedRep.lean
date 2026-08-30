import GroupApproximation.Analysis.VoiculescuAmplifiedAlgebra

/-!
# (V3) The amplified representation `Mₙ(A) → B(K₀ⁿ)`

`Analysis/VoiculescuAmplifiedAlgebra` built `Mₙ(A) ⊆ B(Hⁿ)` by its entries.  A
representation `ρ` of `A` on a finite-dimensional space `K₀` amplifies to a
representation of `Mₙ(A)` on `K₀ⁿ`, applying `ρ` entry by entry, and this module
builds it.  The state Glimm's lemma is fed is the vector state of that
representation at the diagonal vector, so this is the step that makes the state
available.

## The two halves

The entry map `S ↦ (ρ(π_i S ι_j))_{ij}` is a `*`-homomorphism into
`Mₙ(B(K₀))`, and `Analysis/ShulmanFillNormingBlockHom` already has the second
half — the block operator as a unital `*`-homomorphism `Mₙ(B(K₀)) → B(K₀ⁿ)`.  So
the amplified representation is a composition, and the only thing proved here is
that the entry map is a `*`-homomorphism, which is `blockEntry_mul`,
`blockEntry_one` and `blockEntry_star` read one level up.

Nothing here is special to `ρ` being finite-dimensional or faithful: the
amplification of any representation of `A` is a representation of `Mₙ(A)`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {K₀ : Type} [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
  [CompleteSpace K₀]
  {n : ℕ} {A : StarSubalgebra ℂ (H →L[ℂ] H)}

/-! ## The entries, as elements of `A` -/

/-- The `(i,j)` entry of a member of `Mₙ(A)`, as an element of `A`. -/
def blockEntryMem (S : ↥(ampSubalgebra A n)) (i j : Fin n) : ↥A :=
  ⟨blockEntry (S : BlockSpace H n →L[ℂ] BlockSpace H n) i j,
    (mem_ampSubalgebra_iff.mp S.2) i j⟩

@[simp] theorem coe_blockEntryMem (S : ↥(ampSubalgebra A n)) (i j : Fin n) :
    (blockEntryMem S i j : H →L[ℂ] H)
      = blockEntry (S : BlockSpace H n →L[ℂ] BlockSpace H n) i j := rfl

theorem blockEntryMem_zero (i j : Fin n) :
    blockEntryMem (0 : ↥(ampSubalgebra A n)) i j = 0 := by
  apply Subtype.ext
  rw [coe_blockEntryMem]
  show blockEntry (0 : BlockSpace H n →L[ℂ] BlockSpace H n) i j = ((0 : ↥A) : _)
  rw [blockEntry_zero]
  rfl

theorem blockEntryMem_add (S T : ↥(ampSubalgebra A n)) (i j : Fin n) :
    blockEntryMem (S + T) i j = blockEntryMem S i j + blockEntryMem T i j := by
  apply Subtype.ext
  have hc : ((S + T : ↥(ampSubalgebra A n)) : BlockSpace H n →L[ℂ] BlockSpace H n)
      = (S : BlockSpace H n →L[ℂ] BlockSpace H n)
        + (T : BlockSpace H n →L[ℂ] BlockSpace H n) := rfl
  rw [coe_blockEntryMem, hc, blockEntry_add]
  rfl

theorem blockEntryMem_smul (z : ℂ) (S : ↥(ampSubalgebra A n)) (i j : Fin n) :
    blockEntryMem (z • S) i j = z • blockEntryMem S i j := by
  apply Subtype.ext
  rw [coe_blockEntryMem]
  show blockEntry (z • (S : BlockSpace H n →L[ℂ] BlockSpace H n)) i j = _
  rw [blockEntry_smul]
  rfl

theorem blockEntryMem_one (i j : Fin n) :
    blockEntryMem (1 : ↥(ampSubalgebra A n)) i j = if i = j then 1 else 0 := by
  apply Subtype.ext
  rw [coe_blockEntryMem]
  show blockEntry (1 : BlockSpace H n →L[ℂ] BlockSpace H n) i j
      = ((if i = j then (1 : ↥A) else 0 : ↥A) : H →L[ℂ] H)
  rw [blockEntry_one]
  split <;> rfl

theorem blockEntryMem_mul (S T : ↥(ampSubalgebra A n)) (i j : Fin n) :
    blockEntryMem (S * T) i j
      = ∑ r : Fin n, blockEntryMem S i r * blockEntryMem T r j := by
  apply Subtype.ext
  have hc : ((S * T : ↥(ampSubalgebra A n)) : BlockSpace H n →L[ℂ] BlockSpace H n)
      = (S : BlockSpace H n →L[ℂ] BlockSpace H n)
        * (T : BlockSpace H n →L[ℂ] BlockSpace H n) := rfl
  rw [coe_blockEntryMem, hc, blockEntry_mul, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun r _ ↦ rfl

theorem blockEntryMem_star (S : ↥(ampSubalgebra A n)) (i j : Fin n) :
    blockEntryMem (star S) i j = star (blockEntryMem S j i) := by
  apply Subtype.ext
  rw [coe_blockEntryMem]
  show blockEntry (star (S : BlockSpace H n →L[ℂ] BlockSpace H n)) i j = _
  rw [blockEntry_star]
  rfl

/-! ## The entry map as a `*`-homomorphism -/

variable (A) in
/-- The matrix of images of the entries. -/
def ampMatrix (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) (S : ↥(ampSubalgebra A n)) :
    CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀) :=
  fun i j ↦ rho (blockEntryMem S i j)

variable (A) in
@[simp] theorem ampMatrix_apply (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀))
    (S : ↥(ampSubalgebra A n)) (i j : Fin n) :
    ampMatrix A rho S i j = rho (blockEntryMem S i j) := rfl

variable (A) in
/-- **The entry map is a unital `*`-homomorphism `Mₙ(A) → Mₙ(B(K₀))`.** -/
def ampMatrixHom (n : ℕ) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) :
    ↥(ampSubalgebra A n) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀) where
  toFun := ampMatrix A rho
  map_one' := by
    funext i j
    rw [ampMatrix_apply, blockEntryMem_one]
    show _ = (1 : CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀)) i j
    rw [show (1 : CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀)) i j
        = if i = j then 1 else 0 from Matrix.one_apply]
    split
    · exact map_one rho
    · exact map_zero rho
  map_mul' := by
    intro S T
    funext i j
    rw [ampMatrix_apply, blockEntryMem_mul, map_sum]
    show _ = (ampMatrix A rho S * ampMatrix A rho T) i j
    rw [show (ampMatrix A rho S * ampMatrix A rho T) i j
        = ∑ r : Fin n, ampMatrix A rho S i r * ampMatrix A rho T r j from
      Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ ↦ map_mul rho _ _
  map_zero' := by
    funext i j
    rw [ampMatrix_apply, blockEntryMem_zero, map_zero]
    rfl
  map_add' := by
    intro S T
    funext i j
    rw [ampMatrix_apply, blockEntryMem_add, map_add]
    rfl
  commutes' := by
    intro z
    have h1 : (algebraMap ℂ (↥(ampSubalgebra A n))) z
        = z • (1 : ↥(ampSubalgebra A n)) := Algebra.algebraMap_eq_smul_one z
    have h2 : (algebraMap ℂ (CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀))) z
        = z • (1 : CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀)) :=
      Algebra.algebraMap_eq_smul_one z
    rw [h1, h2]
    funext i j
    rw [ampMatrix_apply, blockEntryMem_smul]
    have hz : (z • (1 : CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀))) i j
        = z • ((1 : CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀)) i j) := rfl
    rw [map_smul, blockEntryMem_one, hz,
      show (1 : CStarMatrix (Fin n) (Fin n) (K₀ →L[ℂ] K₀)) i j
        = if i = j then 1 else 0 from Matrix.one_apply, apply_ite rho,
      map_one, map_zero]
  map_star' := by
    intro S
    funext i j
    rw [ampMatrix_apply, blockEntryMem_star, map_star]
    show _ = (star (ampMatrix A rho S)) i j
    rw [CStarMatrix.star_apply]
    rfl

variable (A) in
@[simp] theorem ampMatrixHom_apply (n : ℕ) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀))
    (S : ↥(ampSubalgebra A n)) :
    ampMatrixHom A n rho S = ampMatrix A rho S := rfl

/-! ## The amplified representation -/

variable (A) in
/-- **The amplified representation** `Mₙ(A) → B(K₀ⁿ)`: apply `ρ` entry by entry
and read the matrix as one operator on the block space. -/
def ampRep (n : ℕ) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) :
    ↥(ampSubalgebra A n) →⋆ₐ[ℂ]
      (BlockSpace K₀ n →L[ℂ] BlockSpace K₀ n) :=
  (hBlockOpHom (E := K₀) (n := n)).comp (ampMatrixHom A n rho)

variable (A) in
@[simp] theorem ampRep_apply (n : ℕ) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀))
    (S : ↥(ampSubalgebra A n)) :
    ampRep A n rho S = hBlockOp (ampMatrix A rho S) := rfl

end

end ShulmanFill
end GroupApproximation
