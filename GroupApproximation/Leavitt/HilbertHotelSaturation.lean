import GroupApproximation.Leavitt.HilbertHotelBlocks
import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Tactic.Group

/-!
# The Hilbert-hotel `4m = 16` frame: defect and saturation

This file continues `GroupApproximation.Leavitt.HilbertHotelBlocks`.  With
`U` the branch-map block matrix of the `2m = 8` frame and `V = U⁻¹`, the
Whitehead matrix is

`T = diag(U, V) = diag(U, U⁻¹)`

on the `4m = 16` frame.  Three things are proved here.

* **The boxed conjugation.**  `T` conjugates the corner copy of the elementary
  group by the compression `a ↦ s₀ a r₀`, and it moves the second-block mark
  `1 + E₁₂` to `e₁₂(q) · (mark)`: the complementary idempotent `q = s₁r₁`
  appears out of nothing.
* **The defect.**  `[T·C₀·T⁻¹, e₂₃(1)] = e₁₃(q)`, an elementary matrix which is
  nontrivial exactly because `q ≠ 0`.
* **Saturation.**  `[e₄₁(a r₁), e₁₃(q)] = e₄₃(a r₁ q)` and
  `[e₄₃(a r₁ q), e₃₂(s₁)] = e₄₂(a r₁ q s₁) = e₄₂(a)`: two commutators turn the
  single defect into an *arbitrary* elementary generator, because `r₁ q s₁ = 1`.

All indices are honest elements of `Fin 16`; `flat16` is the ring isomorphism
`M₂(M₂(M₄(R))) ≅ M₁₆(R)` that carries the block frame there, and it sends the
corner `4`-block to the indices `0,1,2,3` and the second block to `4,5,6,7`.

The final section exhibits `T` as an explicit product of elementary
transvections (Whitehead's identity `W(Z)·W(-1) = diag(Z, Z⁻¹)` in the rank-two
frame over `M₈(R)`, flattened), which is what makes the stable letter a concrete
word in the cover presentation downstream.
-/

namespace GroupApproximation
namespace HilbertHotel

open scoped commutatorElement

variable {R : Type*} [Ring R]

/-! ### Two general facts -/

section General

theorem single_map_zero {ι : Type*} [DecidableEq ι] {α β : Type*} [Zero α] [Zero β]
    (f : α → β) (hf : f 0 = 0) (b c : ι) (X : α) :
    (Matrix.single b c X).map f = Matrix.single b c (f X) := by
  ext d e
  rw [Matrix.map_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs
  · rfl
  · exact hf

theorem blockDiag_fst {S : Type*} [NonAssocSemiring S] (B : S) :
    (!![1 + B, 0; 0, 1] : Matrix (Fin 2) (Fin 2) S) = 1 + Matrix.single 0 0 B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockDiag_snd {S : Type*} [NonAssocSemiring S] (C : S) :
    (!![1, 0; 0, 1 + C] : Matrix (Fin 2) (Fin 2) S) = 1 + Matrix.single 1 1 C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockDiag_both {S : Type*} [NonAssocSemiring S] (B C : S) :
    (!![1 + B, 0; 0, 1 + C] : Matrix (Fin 2) (Fin 2) S)
      = 1 + (Matrix.single 0 0 B + Matrix.single 1 1 C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Block-diagonal matrices with an identity second block multiply blockwise. -/
theorem blockDiagOne_mul {S : Type*} [NonAssocSemiring S] (M N : S) :
    (!![M, 0; 0, 1] : Matrix (Fin 2) (Fin 2) S) * !![N, 0; 0, 1] = !![M * N, 0; 0, 1] := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockDiagOne_one {S : Type*} [NonAssocSemiring S] :
    (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) S) = 1 :=
  Matrix.one_fin_two.symm

/-- Two elementary matrices whose index pairs do not chain commute. -/
theorem elementaryUnit_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    elementaryUnit i j hij a * elementaryUnit k l hkl b
      = elementaryUnit k l hkl b * elementaryUnit i j hij a := by
  apply Units.ext
  change (1 + Matrix.single i j a) * (1 + Matrix.single k l b)
    = (1 + Matrix.single k l b) * (1 + Matrix.single i j a)
  have h₁ : Matrix.single i j a * Matrix.single k l b = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j k hjk b
  have h₂ : Matrix.single k l b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) k l i hli a
  noncomm_ring [h₁, h₂]

theorem commutator_mul_left_of_commute {G : Type*} [Group G] (x y z : G) (h : Commute y z) :
    ⁅x * y, z⁆ = ⁅x, z⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have hxyz : x * y * z = x * z * y := by rw [mul_assoc, h.eq, ← mul_assoc]
  rw [hxyz]
  group

end General

/-! ### The Whitehead matrix on the `4m = 16` frame -/

section Frame16

variable (L : LeavittFamily R)

/-- `T = diag(U, V) = diag(U, U⁻¹)`, in the doubly nested block frame
`M₂(M₂(M₄(R)))`. -/
def T16 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)) :=
  !![U8 L, 0; 0, V8 L]

/-- The inverse Whitehead matrix `diag(V, U)`. -/
def T16inv : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)) :=
  !![V8 L, 0; 0, U8 L]

theorem T16_mul_T16inv : T16 L * T16inv L = 1 := by
  unfold T16 T16inv
  rw [Matrix.mul_fin_two, U8_mul_V8, V8_mul_U8]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  exact Matrix.one_fin_two.symm

theorem T16inv_mul_T16 : T16inv L * T16 L = 1 := by
  unfold T16 T16inv
  rw [Matrix.mul_fin_two, U8_mul_V8, V8_mul_U8]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  exact Matrix.one_fin_two.symm

/-- **The boxed conjugation of section 9**, in block form: `T` acts on the whole
first half by conjugation by the branch map `U`, and trivially on the second. -/
theorem T16_conj (Y : Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)) :
    T16 L * !![Y, 0; 0, 1] * T16inv L = !![U8 L * Y * V8 L, 0; 0, 1] := by
  have h1 : T16 L * !![Y, 0; 0, 1] = !![U8 L * Y, 0; 0, V8 L] := by
    unfold T16
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h1]
  unfold T16inv
  rw [Matrix.mul_fin_two, V8_mul_U8]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Conjugation compresses the corner copy of an elementary generator. -/
theorem T16_conj_corner (a : R) (i j : Fin 4) :
    T16 L * !![!![1 + Matrix.single i j a, 0; 0, 1], 0; 0, 1] * T16inv L
      = !![!![1 + Matrix.single i j (L.s0 * a * L.t0), 0; 0, 1], 0; 0, 1] := by
  rw [T16_conj, compression_elementary]

/-- Conjugation moves the commuting second-block mark and deposits `e₁₂(q)` in
the corner. -/
theorem T16_conj_mark :
    T16 L * !![!![1, 0; 0, mark R], 0; 0, 1] * T16inv L
      = !![!![1 + Matrix.single 0 1 L.p1, 0; 0, mark R], 0; 0, 1] := by
  rw [T16_conj, movedCentralizer_mark]

end Frame16

/-! ### Flattening to `M₁₆(R)` -/

section Flatten

/-- The index identification of the `4m` frame: block `b` of the half `h` at
position `k` is the index `k + 4h + 8b`.  The corner `4`-block is `0,1,2,3` and
the second block of the first half is `4,5,6,7`. -/
def frame16 : Fin 2 × (Fin 2 × Fin 4) ≃ Fin 16 where
  toFun x := ⟨x.2.2.val + 4 * x.2.1.val + 8 * x.1.val, by
    have h1 := x.1.isLt
    have h2 := x.2.1.isLt
    have h3 := x.2.2.isLt
    omega⟩
  invFun n := (⟨n.val / 8, by have := n.isLt; omega⟩,
    (⟨n.val / 4 % 2, by omega⟩, ⟨n.val % 4, by omega⟩))
  left_inv := by decide
  right_inv := by decide

/-- The corner embedding `Fin 4 ↪ Fin 16` of the first `m`-block. -/
def corner (i : Fin 4) : Fin 16 := ⟨i.val, by have := i.isLt; omega⟩

theorem frame16_corner (i : Fin 4) : frame16 (0, (0, i)) = corner i := rfl

theorem corner_injective : Function.Injective corner := by
  intro i j h
  have hv : (corner i).val = (corner j).val := congrArg Fin.val h
  exact Fin.val_injective hv

theorem corner_ne {i j : Fin 4} (h : i ≠ j) : corner i ≠ corner j :=
  fun hc => h (corner_injective hc)

/-- `M₂(M₂(M₄(R))) ≅ M₁₆(R)`. -/
def flat16 (R : Type*) [Ring R] :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R))
      ≃+* Matrix (Fin 16) (Fin 16) R :=
  (((Matrix.compRingEquiv (Fin 2) (Fin 4) R).mapMatrix (m := Fin 2)).trans
    (Matrix.compRingEquiv (Fin 2) (Fin 2 × Fin 4) R)).trans
      (Matrix.reindexRingEquiv R frame16)

theorem flat16_apply
    (M : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R))) :
    flat16 R M = Matrix.reindexRingEquiv R frame16
      (Matrix.compRingEquiv (Fin 2) (Fin 2 × Fin 4) R
        (((Matrix.compRingEquiv (Fin 2) (Fin 4) R).mapMatrix (m := Fin 2)) M)) := rfl

theorem flat16_single (b c b' c' : Fin 2) (i j : Fin 4) (x : R) :
    flat16 R (Matrix.single b c (Matrix.single b' c' (Matrix.single i j x)))
      = Matrix.single (frame16 (b, (b', i))) (frame16 (c, (c', j))) x := by
  have hinner : (Matrix.compRingEquiv (Fin 2) (Fin 4) R)
      (Matrix.single b' c' (Matrix.single i j x))
      = Matrix.single (b', i) (c', j) x := by
    rw [Matrix.compRingEquiv_apply, Matrix.comp_single_single]
  rw [flat16_apply, RingEquiv.mapMatrix_apply,
    single_map_zero _ (map_zero (Matrix.compRingEquiv (Fin 2) (Fin 4) R)), hinner,
    Matrix.compRingEquiv_apply, Matrix.comp_single_single, Matrix.coe_reindexRingEquiv,
    Matrix.reindex_apply, Matrix.submatrix_single_equiv, Equiv.symm_symm]

end Flatten

/-! ### The boxed conjugation on `M₁₆(R)` -/

section Flat16

variable (L : LeavittFamily R)

/-- The Whitehead matrix as an honest `16 × 16` matrix. -/
def T : Matrix (Fin 16) (Fin 16) R := flat16 R (T16 L)

/-- Its inverse. -/
def Tinv : Matrix (Fin 16) (Fin 16) R := flat16 R (T16inv L)

theorem T_mul_Tinv : T L * Tinv L = 1 := by
  rw [T, Tinv, ← map_mul, T16_mul_T16inv, map_one]

theorem Tinv_mul_T : Tinv L * T L = 1 := by
  rw [T, Tinv, ← map_mul, T16inv_mul_T16, map_one]

/-- `T ∈ GL₁₆(R)`. -/
def Tunit : (Matrix (Fin 16) (Fin 16) R)ˣ where
  val := T L
  inv := Tinv L
  val_inv := T_mul_Tinv L
  inv_val := Tinv_mul_T L

@[simp] theorem Tunit_val : (Tunit L : Matrix (Fin 16) (Fin 16) R) = T L := rfl

@[simp] theorem Tunit_inv_val : Units.val (Tunit L)⁻¹ = Tinv L := rfl

/-! #### Transport of the two conjugation identities -/

theorem flat16_corner_elementary (a : R) (i j : Fin 4) :
    flat16 R (!![!![1 + Matrix.single i j a, 0; 0, 1], 0; 0, 1])
      = 1 + Matrix.single (corner i) (corner j) a := by
  rw [blockDiag_fst, blockDiag_fst, map_add, map_one, flat16_single, frame16_corner,
    frame16_corner]

theorem flat16_mark :
    flat16 R (!![!![1, 0; 0, mark R], 0; 0, 1])
      = 1 + Matrix.single (4 : Fin 16) 5 1 := by
  rw [mark, blockDiag_snd, blockDiag_fst, map_add, map_one, flat16_single]
  rfl

theorem flat16_defect :
    flat16 R (!![!![1 + Matrix.single 0 1 L.p1, 0; 0, mark R], 0; 0, 1])
      = 1 + Matrix.single (0 : Fin 16) 1 L.p1 + Matrix.single (4 : Fin 16) 5 1 := by
  rw [mark, blockDiag_both, blockDiag_fst, map_add, map_one, Matrix.single_add,
    map_add, flat16_single, flat16_single, add_assoc]
  rfl

/-- **Compression on the `16` frame.**  Conjugation by the Whitehead matrix
compresses every corner elementary generator: `T e_{ij}(a) T⁻¹ = e_{ij}(s₀ a r₀)`
for `i, j` in the corner `4`-block. -/
theorem Tunit_conj_corner (a : R) (i j : Fin 4) (h : corner i ≠ corner j) :
    Tunit L * elementaryUnit (corner i) (corner j) h a * (Tunit L)⁻¹
      = elementaryUnit (corner i) (corner j) h (L.s0 * a * L.t0) := by
  apply Units.ext
  show T L * (1 + Matrix.single (corner i) (corner j) a) * Tinv L
    = 1 + Matrix.single (corner i) (corner j) (L.s0 * a * L.t0)
  rw [← flat16_corner_elementary, T, Tinv, ← map_mul, ← map_mul, T16_conj_corner,
    flat16_corner_elementary]

/-- **The boxed conjugation of section 9.**  The commuting second-block mark
`e₄₅(1)` is carried by the Whitehead matrix to `e₁₂(q)·e₄₅(1)`: the corner factor
`e₁₂(q)` is the compression defect, and it is there because the mark's entries are
central. -/
theorem Tunit_conj_mark (h45 : (4 : Fin 16) ≠ 5) (h01 : (0 : Fin 16) ≠ 1) :
    Tunit L * elementaryUnit (4 : Fin 16) 5 h45 1 * (Tunit L)⁻¹
      = elementaryUnit (0 : Fin 16) 1 h01 L.p1 * elementaryUnit (4 : Fin 16) 5 h45 1 := by
  apply Units.ext
  show T L * (1 + Matrix.single (4 : Fin 16) 5 1) * Tinv L
    = (1 + Matrix.single (0 : Fin 16) 1 L.p1) * (1 + Matrix.single (4 : Fin 16) 5 1)
  have hcross : (Matrix.single (0 : Fin 16) (1 : Fin 16) L.p1
      * Matrix.single (4 : Fin 16) (5 : Fin 16) 1 : Matrix (Fin 16) (Fin 16) R) = 0 := by
    apply Matrix.single_mul_single_of_ne
    decide
  have hleft : T L * (1 + Matrix.single (4 : Fin 16) 5 1) * Tinv L
      = 1 + Matrix.single (0 : Fin 16) 1 L.p1 + Matrix.single (4 : Fin 16) 5 1 := by
    rw [← flat16_mark, T, Tinv, ← map_mul, ← map_mul, T16_conj_mark, flat16_defect]
  rw [hleft]
  noncomm_ring [hcross]

end Flat16

/-! ### The corner embedding of the rank-`m` elementary group

`cornerBlock M` is the note's `C`: the block-diagonal `16 × 16` matrix
`diag(M, I₄, I₄, I₄)`.  It is multiplicative and unital but *not* additive, so it
is packaged as a monoid homomorphism, and on the unit groups it carries the
rank-four elementary group into the rank-sixteen one along `corner`.  This is the
arrow `ι : Λ → H₀` of the compression datum. -/

section CornerEmbedding

/-- The corner `4`-block embedding `M₄(R) → M₁₆(R)`, `M ↦ diag(M, I)`. -/
def cornerBlock (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 16) (Fin 16) R :=
  flat16 R !![!![M, 0; 0, 1], 0; 0, 1]

theorem cornerBlock_mul (M N : Matrix (Fin 4) (Fin 4) R) :
    cornerBlock (M * N) = cornerBlock M * cornerBlock N := by
  unfold cornerBlock
  rw [← blockDiagOne_mul M N, ← blockDiagOne_mul, map_mul]

theorem cornerBlock_one : cornerBlock (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  unfold cornerBlock
  rw [blockDiagOne_one, blockDiagOne_one, map_one]

/-- The corner block embedding as a monoid homomorphism. -/
def cornerBlockHom : Matrix (Fin 4) (Fin 4) R →* Matrix (Fin 16) (Fin 16) R where
  toFun := cornerBlock
  map_one' := cornerBlock_one
  map_mul' := cornerBlock_mul

/-- The corner embedding on unit groups, `GL₄(R) →* GL₁₆(R)`. -/
def cornerUnits : (Matrix (Fin 4) (Fin 4) R)ˣ →* (Matrix (Fin 16) (Fin 16) R)ˣ :=
  Units.map (cornerBlockHom (R := R))

/-- The corner embedding takes elementary generators to elementary generators,
with indices shifted along `corner`. -/
theorem cornerUnits_elementaryUnit (i j : Fin 4) (h : i ≠ j) (a : R) :
    cornerUnits (elementaryUnit i j h a)
      = elementaryUnit (corner i) (corner j) (corner_ne h) a := by
  apply Units.ext
  show cornerBlock (1 + Matrix.single i j a)
    = 1 + Matrix.single (corner i) (corner j) a
  exact flat16_corner_elementary a i j

theorem cornerUnits_map_le :
    (elementaryGroup (Fin 4) R).map cornerUnits ≤ elementaryGroup (Fin 16) R := by
  rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change cornerUnits (elementaryUnit i j hij a) ∈ elementaryGroup (Fin 16) R
  rw [cornerUnits_elementaryUnit]
  exact elementaryUnit_mem _ _ _ a

/-- **The corner embedding** `EL₄(R) →* EL₁₆(R)`. -/
def cornerEmbedding : elementaryGroup (Fin 4) R →* elementaryGroup (Fin 16) R :=
  ((cornerUnits (R := R)).comp (elementaryGroup (Fin 4) R).subtype).codRestrict
    (elementaryGroup (Fin 16) R) fun g =>
      cornerUnits_map_le
        (Subgroup.apply_coe_mem_map (cornerUnits (R := R)) (elementaryGroup (Fin 4) R) g)

@[simp] theorem cornerEmbedding_apply (g : elementaryGroup (Fin 4) R) :
    (cornerEmbedding g : (Matrix (Fin 16) (Fin 16) R)ˣ) = cornerUnits (g : _) := rfl

theorem cornerEmbedding_elementaryUnit (i j : Fin 4) (h : i ≠ j) (a : R) :
    (cornerEmbedding ⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩ :
        (Matrix (Fin 16) (Fin 16) R)ˣ)
      = elementaryUnit (corner i) (corner j) (corner_ne h) a :=
  cornerUnits_elementaryUnit i j h a

/-- No corner index reaches the second block. -/
theorem corner_ne_of_four_le (i : Fin 4) (k : Fin 16) (hk : 4 ≤ k.val) :
    corner i ≠ k := by
  intro h
  have h2 : (corner i).val = k.val := congrArg Fin.val h
  have h3 : (corner i).val = i.val := rfl
  have hi := i.isLt
  omega

/-- **The mark centralizes the corner.**  `e₄₅(1)` lives in the second block, whose
indices are disjoint from the corner's, so it commutes with the whole corner copy
of the rank-four elementary group.  This is the `[c, ι(Λ)] = 1` clause of the
compression datum. -/
theorem cornerUnits_commute_mark (h45 : (4 : Fin 16) ≠ 5)
    (g : (Matrix (Fin 4) (Fin 4) R)ˣ) (hg : g ∈ elementaryGroup (Fin 4) R) :
    Commute (cornerUnits g) (elementaryUnit (4 : Fin 16) 5 h45 1) := by
  rw [elementaryGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [cornerUnits_elementaryUnit]
      exact elementaryUnit_commute (corner_ne hij) h45
        (corner_ne_of_four_le j 4 (by decide))
        ((corner_ne_of_four_le i 5 (by decide)).symm) a 1
  | one =>
      rw [map_one]
      exact Commute.one_left _
  | mul x y _ _ hx hy =>
      rw [map_mul]
      exact hx.mul_left hy
  | inv x _ hx =>
      rw [map_inv]
      exact hx.inv_left

end CornerEmbedding

/-! ### The defect and its nontriviality -/

section Defect

variable (L : LeavittFamily R)

/-- **The defect computation of section 10.**  Commuting the moved mark against
the corner generator `e₂₃(1)` kills the second-block factor and leaves exactly
`e₁₃(q)`. -/
theorem defect_commutator
    (h01 : (0 : Fin 16) ≠ 1) (h45 : (4 : Fin 16) ≠ 5) (h12 : (1 : Fin 16) ≠ 2)
    (h02 : (0 : Fin 16) ≠ 2) :
    ⁅elementaryUnit (0 : Fin 16) 1 h01 L.p1 * elementaryUnit (4 : Fin 16) 5 h45 1,
      elementaryUnit (1 : Fin 16) 2 h12 1⁆
      = elementaryUnit (0 : Fin 16) 2 h02 L.p1 := by
  have hcomm : Commute (elementaryUnit (4 : Fin 16) 5 h45 (1 : R))
      (elementaryUnit (1 : Fin 16) 2 h12 (1 : R)) :=
    elementaryUnit_commute h45 h12 (by decide) (by decide) 1 1
  rw [commutator_mul_left_of_commute _ _ _ hcomm,
    elementaryUnit_commutator (0 : Fin 16) 1 2 h01 h12 h02, mul_one]

/-- The same computation started from the mark itself: conjugating the mark by
the Whitehead matrix and commuting the result against the corner generator
`e₂₃(1)` produces the defect `e₁₃(q)`. -/
theorem defect_from_conjugated_mark
    (h01 : (0 : Fin 16) ≠ 1) (h45 : (4 : Fin 16) ≠ 5) (h12 : (1 : Fin 16) ≠ 2)
    (h02 : (0 : Fin 16) ≠ 2) :
    ⁅Tunit L * elementaryUnit (4 : Fin 16) 5 h45 1 * (Tunit L)⁻¹,
      elementaryUnit (1 : Fin 16) 2 h12 1⁆
      = elementaryUnit (0 : Fin 16) 2 h02 L.p1 := by
  rw [Tunit_conj_mark L h45 h01, defect_commutator L h01 h45 h12 h02]

/-- `e₁₃(q) ≠ 1`: the defect is a genuinely nontrivial element, because the
complementary idempotent `q = s₁r₁` is nonzero. -/
theorem defect_ne_one [Nontrivial R] (h02 : (0 : Fin 16) ≠ 2) :
    elementaryUnit (0 : Fin 16) 2 h02 L.p1 ≠ 1 := by
  intro hcon
  refine q_ne_zero L (elementaryUnit_injective (0 : Fin 16) 2 h02 ?_)
  rw [hcon, elementaryUnit_zero]

/-! ### Saturation: two commutators reach every elementary generator -/

/-- **Saturation, first step.**  `[e₄₁(a r₁), e₁₃(q)] = e₄₃(a r₁ q)`. -/
theorem saturation_step_one (a : R)
    (h30 : (3 : Fin 16) ≠ 0) (h02 : (0 : Fin 16) ≠ 2) (h32 : (3 : Fin 16) ≠ 2) :
    ⁅elementaryUnit (3 : Fin 16) 0 h30 (a * L.t1),
      elementaryUnit (0 : Fin 16) 2 h02 L.p1⁆
      = elementaryUnit (3 : Fin 16) 2 h32 (a * L.t1 * L.p1) :=
  elementaryUnit_commutator (3 : Fin 16) 0 2 h30 h02 h32 (a * L.t1) L.p1

/-- **Saturation, second step.**  `[e₄₃(a r₁ q), e₃₂(s₁)] = e₄₂(a r₁ q s₁) = e₄₂(a)`:
fullness `r₁ q s₁ = 1` converts the defect into an *arbitrary* coefficient. -/
theorem saturation_step_two (a : R)
    (h32 : (3 : Fin 16) ≠ 2) (h21 : (2 : Fin 16) ≠ 1) (h31 : (3 : Fin 16) ≠ 1) :
    ⁅elementaryUnit (3 : Fin 16) 2 h32 (a * L.t1 * L.p1),
      elementaryUnit (2 : Fin 16) 1 h21 L.s1⁆
      = elementaryUnit (3 : Fin 16) 1 h31 a := by
  have key : a * L.t1 * L.p1 * L.s1 = a := by
    rw [mul_assoc, mul_assoc, ← mul_assoc L.t1, r1_mul_q_mul_s1, mul_one]
  rw [elementaryUnit_commutator (3 : Fin 16) 2 1 h32 h21 h31, key]

/-- **The saturation chain.**  Starting from the single defect `e₁₃(q)`, two
commutators with elements of the elementary group produce `e₄₂(a)` for an
arbitrary `a : R`. -/
theorem saturation_chain (a : R)
    (h30 : (3 : Fin 16) ≠ 0) (h02 : (0 : Fin 16) ≠ 2) (h32 : (3 : Fin 16) ≠ 2)
    (h21 : (2 : Fin 16) ≠ 1) (h31 : (3 : Fin 16) ≠ 1) :
    ⁅⁅elementaryUnit (3 : Fin 16) 0 h30 (a * L.t1),
        elementaryUnit (0 : Fin 16) 2 h02 L.p1⁆,
      elementaryUnit (2 : Fin 16) 1 h21 L.s1⁆
      = elementaryUnit (3 : Fin 16) 1 h31 a := by
  rw [saturation_step_one L a h30 h02 h32, saturation_step_two L a h32 h21 h31]

/-- **The saturation chain at an arbitrary frame.**  The chain uses only four
distinct indices, the elementary commutator relation, and fullness
`r₁ q s₁ = 1`, so it holds in `EL_ι(R)` for every finite index type: the defect
`e_{xy}(q)` together with `e_{dx}(a r₁)` and `e_{yz}(s₁)` produces `e_{dz}(a)`
for an arbitrary coefficient.  Instantiating at `ι = Fin 16` with
`d, x, y, z = 3, 0, 2, 1` recovers `saturation_chain`.

This is the *constructive* route to saturation in the model, and it is kept
deliberately even though the shortest path does not use it.  The short path
pushes `BinaryLeavittSteinberg.normalClosure_root_eq_top` (rank `≥ 5`, any root,
any nonzero coefficient) forward along the Steinberg-to-elementary projection;
that is quicker but puts `St_n(R)` and `projection_surjective` on the critical
path.  The chain above proves the same normal-generation statement directly
inside `EL_ι(R)`, with explicit words, so it is what replaces the Steinberg
detour if that dependency is ever unwanted.

A caution on how far either statement reaches: both are theorems about the
*model*.  Along a surjection `G ↠ M` a normal closure only pushes forward, so
`⟪d̄⟫ = M` gives `⟪d⟫ · ker = G`, not `⟪d⟫ = G`.  In a cover presentation the
saturation must still be imposed as relators; what the model supplies is their
consistency, and the existence of the words they name. -/
theorem saturation_chain_generic {ι : Type*} [Fintype ι] [DecidableEq ι] (a : R)
    (d x y z : ι) (hdx : d ≠ x) (hxy : x ≠ y) (hdy : d ≠ y) (hyz : y ≠ z)
    (hdz : d ≠ z) :
    ⁅⁅elementaryUnit d x hdx (a * L.t1), elementaryUnit x y hxy L.p1⁆,
      elementaryUnit y z hyz L.s1⁆
      = elementaryUnit d z hdz a := by
  have key : a * L.t1 * L.p1 * L.s1 = a := by
    rw [mul_assoc, mul_assoc, ← mul_assoc L.t1, r1_mul_q_mul_s1, mul_one]
  rw [elementaryUnit_commutator d x y hdx hxy hdy (a * L.t1) L.p1,
    elementaryUnit_commutator d y z hdy hyz hdz (a * L.t1 * L.p1) L.s1, key]

end Defect

end HilbertHotel
end GroupApproximation
