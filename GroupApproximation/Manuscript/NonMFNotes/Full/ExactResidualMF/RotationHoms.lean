import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidualMF.RotationBlock
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidualMF.Gluing
import GroupApproximation.Sofic.DirectSumAmplification
import GroupApproximation.Sofic.NormTraceGap

/-!
# The two unitary families of the rotation construction

Source: `non_mf_group_notes.tex`, proof of `thm:exact-mf-residual`, and
Shulman (arXiv:2603.13564), proof of Theorem 10.  Given two finite actions
`α`, `β` of `G` on `Y`, the first copy of `G` acts on `ℂ^Y ⊕ ℂ^Y` by
`pairHom g = diag (P_{α g}, P_{β g})`, and the second copy by the conjugate
`V⁻¹ (pairHom g) V` of the same representation by a rotation `V`.

This file proves:

* `opLength_inv_mul_rotConjHom`: the operator distance between the two
  families at `g` is the norm of the commutator `V P - P V`;
* the basis-column calculus `ColE`: on core points (`c = 0`, `s = 1`) the
  first family moves `e_{inl v}` to `e_{inl (α g v)}` and the second family
  moves it to `e_{inl (β g v)}`, so a word follows its letters;
* `one_le_opLength_of_colE`: a unitary moving a basis vector to a different
  basis vector is at operator distance at least one from the identity.
-/

namespace GroupApproximation.Full.NN01b

open GroupApproximation Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Basis columns -/

/-- `ColE A j i`: the matrix `A` sends the basis vector `e_j` to `e_i`. -/
structure ColE {ι : Type*} (A : Matrix ι ι ℂ) (j i : ι) : Prop where
  diag : A i j = 1
  off : ∀ k, k ≠ i → A k j = 0

theorem colE_one {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    ColE (1 : Matrix ι ι ℂ) j j :=
  ⟨Matrix.one_apply_eq j, fun _ hk => Matrix.one_apply_ne hk⟩

theorem colE_mul_apply {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ} {j k : ι}
    (hB : ColE B k j) (m : ι) : (A * B) m k = A m j := by
  rw [Matrix.mul_apply]
  calc ∑ l, A m l * B l k = A m j * B j k :=
        Finset.sum_eq_single j
          (fun l _ hl => show A m l * B l k = 0 by rw [hB.off l hl, mul_zero])
          (fun hj => absurd (Finset.mem_univ j) hj)
    _ = A m j := by rw [hB.diag, mul_one]

theorem colE_mul {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ} {i j k : ι}
    (hA : ColE A j i) (hB : ColE B k j) : ColE (A * B) k i :=
  ⟨(colE_mul_apply hB i).trans hA.diag, fun m hm => (colE_mul_apply hB m).trans (hA.off m hm)⟩

section Words

variable {G : Type} [Group G]

/-- A word of matrices follows its letters on basis vectors. -/
theorem colE_wordEval {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Bool → G → Matrix ι ι ℂ)
    (pt : List (Bool × G) → ι) (l : List (Bool × G)) :
    (∀ (p : Bool × G) (l' : List (Bool × G)), p :: l' <:+ l →
      ColE (M p.1 p.2) (pt l') (pt (p :: l'))) →
    ColE (wordEval G M l) (pt []) (pt l) := by
  induction l with
  | nil =>
    intro _
    rw [wordEval_nil]
    exact colE_one (pt [])
  | cons p l ih =>
    intro h
    rw [wordEval_cons]
    exact colE_mul (h p l (List.suffix_refl _))
      (ih fun q l' hq => h q l' (hq.trans (List.suffix_cons p l)))

end Words

/-- A unitary sending `e_j` to `e_i ≠ e_j` has operator distance at least one
from the identity. -/
theorem one_le_opLength_of_colE {X : FiniteModel} (u : Matrix.unitaryGroup X ℂ) {j i : X}
    (h : ColE (u : Matrix X X ℂ) j i) (hij : i ≠ j) : 1 ≤ opLength X u := by
  show 1 ≤ ‖(u : Matrix X X ℂ) - 1‖
  have hentry : ((u : Matrix X X ℂ) - 1) j j = -1 := by
    rw [Matrix.sub_apply, h.off j (Ne.symm hij), Matrix.one_apply_eq, zero_sub]
  have hsq : (1 : ℝ) ≤ ‖(u : Matrix X X ℂ) - 1‖ ^ 2 := by
    have hle := normSq_entry_le_sq_l2_opNorm X ((u : Matrix X X ℂ) - 1) j j
    rw [hentry, Complex.normSq_neg, Complex.normSq_one] at hle
    exact hle
  by_contra hlt
  exact absurd hsq (not_le.mpr (pow_lt_one₀ (norm_nonneg _) (not_le.mp hlt) two_ne_zero))

theorem coe_unitaryGroup_inv {X : FiniteModel} (V : Matrix.unitaryGroup X ℂ) :
    ((V⁻¹ : Matrix.unitaryGroup X ℂ) : Matrix X X ℂ) = (V : Matrix X X ℂ)ᴴ :=
  Matrix.star_eq_conjTranspose (V : Matrix X X ℂ)

variable (Y : FiniteModel)

/-! ## Columns of the building blocks -/

theorem colE_pmat (σ : Equiv.Perm Y) (w : Y) : ColE (pmat Y σ) w (σ w) := by
  refine ⟨?_, fun k hk => ?_⟩
  · have hw : σ⁻¹ (σ w) = w := Equiv.Perm.inv_eq_iff_eq.mpr rfl
    rw [pmat_apply, if_pos hw]
  · have hkw : ¬σ⁻¹ k = w := fun hkw => hk (Equiv.Perm.inv_eq_iff_eq.mp hkw)
    rw [pmat_apply, if_neg hkw]

theorem colE_blockDiag_inl {A B : Matrix Y Y ℂ} {j i : Y} (h : ColE A j i) :
    ColE (blockDiagMatrix Y Y A B) (Sum.inl j) (Sum.inl i) := by
  unfold blockDiagMatrix
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Matrix.fromBlocks_apply₁₁]
    exact h.diag
  · rcases k with k | k
    · rw [Matrix.fromBlocks_apply₁₁]
      exact h.off k (fun hki => hk (congrArg Sum.inl hki))
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem colE_blockDiag_inr {A B : Matrix Y Y ℂ} {j i : Y} (h : ColE B j i) :
    ColE (blockDiagMatrix Y Y A B) (Sum.inr j) (Sum.inr i) := by
  unfold blockDiagMatrix
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Matrix.fromBlocks_apply₂₂]
    exact h.diag
  · rcases k with k | k
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    · rw [Matrix.fromBlocks_apply₂₂]
      exact h.off k (fun hki => hk (congrArg Sum.inr hki))

/-- On a core point the rotation sends `e_{inl v}` to `e_{inr v}`. -/
theorem colE_rotMatrix_inl (c s : Y → ℝ) (v : Y) (hc : c v = 0) (hs : s v = 1) :
    ColE (rotMatrix Y c s) (Sum.inl v) (Sum.inr v) := by
  unfold rotMatrix rdiag
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.diagonal_apply_eq, hs, Complex.ofReal_one]
  · rcases k with k | k
    · rw [Matrix.fromBlocks_apply₁₁]
      by_cases hkv : k = v
      · rw [hkv, Matrix.diagonal_apply_eq, hc, Complex.ofReal_zero]
      · exact Matrix.diagonal_apply_ne _ hkv
    · rw [Matrix.fromBlocks_apply₂₁]
      exact Matrix.diagonal_apply_ne _ (fun hkv => hk (congrArg Sum.inr hkv))

/-- On a core point the inverse rotation sends `e_{inr v}` to `e_{inl v}`. -/
theorem colE_rotMatrix_conjTranspose_inr (c s : Y → ℝ) (v : Y) (hc : c v = 0) (hs : s v = 1) :
    ColE (rotMatrix Y c s)ᴴ (Sum.inr v) (Sum.inl v) := by
  rw [rotMatrix_conjTranspose]
  unfold rdiag
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply_eq, hs, Complex.ofReal_one]
  · rcases k with k | k
    · rw [Matrix.fromBlocks_apply₁₂]
      exact Matrix.diagonal_apply_ne _ (fun hkv => hk (congrArg Sum.inl hkv))
    · rw [Matrix.fromBlocks_apply₂₂]
      by_cases hkv : k = v
      · rw [hkv, Matrix.diagonal_apply_eq, hc, Complex.ofReal_zero]
      · exact Matrix.diagonal_apply_ne _ hkv

/-! ## The two families -/

variable {G : Type} [Group G]

/-- `g ↦ diag (P_{α g}, P_{β g})` on `ℂ^Y ⊕ ℂ^Y`. -/
def pairHom (α β : G →* Equiv.Perm Y) : G →* Matrix.unitaryGroup (blockSumModel Y Y) ℂ :=
  (DirectSumAmplification.blockDiagHom Y Y).comp
    (((permUnitaryHom Y).comp α).prod ((permUnitaryHom Y).comp β))

theorem coe_pairHom (α β : G →* Equiv.Perm Y) (g : G) :
    ((pairHom Y α β g : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) =
      blockDiagMatrix Y Y (pmat Y (α g)) (pmat Y (β g)) := rfl

/-- The rotation `[[C, -S], [S, C]]` as a unitary. -/
def rotUnitary (c s : Y → ℝ) (hcs : ∀ w, c w * c w + s w * s w = 1) :
    Matrix.unitaryGroup (blockSumModel Y Y) ℂ :=
  ⟨rotMatrix Y c s, rotMatrix_mem_unitaryGroup Y c s hcs⟩

theorem coe_rotUnitary (c s : Y → ℝ) (hcs : ∀ w, c w * c w + s w * s w = 1) :
    ((rotUnitary Y c s hcs : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) = rotMatrix Y c s := rfl

/-- The conjugate representation `g ↦ V⁻¹ ρ(g) V`. -/
def rotConjHom (V : Matrix.unitaryGroup (blockSumModel Y Y) ℂ)
    (ρ : G →* Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
    G →* Matrix.unitaryGroup (blockSumModel Y Y) ℂ where
  toFun g := V⁻¹ * ρ g * V
  map_one' := by
    show V⁻¹ * ρ 1 * V = 1
    rw [map_one, mul_one, inv_mul_cancel]
  map_mul' g h := by
    show V⁻¹ * ρ (g * h) * V = V⁻¹ * ρ g * V * (V⁻¹ * ρ h * V)
    rw [map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem coe_rotConjHom (V : Matrix.unitaryGroup (blockSumModel Y Y) ℂ)
    (ρ : G →* Matrix.unitaryGroup (blockSumModel Y Y) ℂ) (g : G) :
    ((rotConjHom Y V ρ g : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) =
      ((V⁻¹ : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
          Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
        (ρ g : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
          (V : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) := rfl

/-- The distance between the two families is the commutator norm
(`thm:exact-mf-residual`, `non_mf_group_notes.tex`). -/
theorem opLength_inv_mul_rotConjHom (V : Matrix.unitaryGroup (blockSumModel Y Y) ℂ)
    (ρ : G →* Matrix.unitaryGroup (blockSumModel Y Y) ℂ) (g : G) :
    opLength (blockSumModel Y Y) ((ρ g)⁻¹ * rotConjHom Y V ρ g) =
      ‖(V : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
          (ρ g : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) -
        (ρ g : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
          (V : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ)‖ := by
  rw [opLength_inv_mul]
  have hWW' : (V : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
      ((V⁻¹ : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel V)
  have hsplit : (V : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
      (((rotConjHom Y V ρ g : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
          Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) -
        (ρ g : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ)) =
      (ρ g : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
          (V : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) -
        (V : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) *
          (ρ g : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) := by
    rw [coe_rotConjHom, mul_sub, ← mul_assoc, ← mul_assoc, hWW', one_mul]
  rw [← CStarRing.norm_mem_unitary_mul
      (((rotConjHom Y V ρ g : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
          Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) -
        (ρ g : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ)) V.2,
    hsplit, norm_sub_rev]

/-- Letters of the first copy on the `inl` sheet. -/
theorem colE_pairHom (α β : G →* Equiv.Perm Y) (g : G) (v : Y) :
    ColE ((pairHom Y α β g : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) (Sum.inl v) (Sum.inl (α g v)) := by
  rw [coe_pairHom]
  exact colE_blockDiag_inl Y (colE_pmat Y (α g) v)

/-- Letters of the second copy on the `inl` sheet, between core points. -/
theorem colE_rotConjHom (α β : G →* Equiv.Perm Y) (c s : Y → ℝ)
    (hcs : ∀ w, c w * c w + s w * s w = 1) (g : G) (v : Y)
    (hc : c v = 0) (hs : s v = 1) (hc' : c (β g v) = 0) (hs' : s (β g v) = 1) :
    ColE ((rotConjHom Y (rotUnitary Y c s hcs) (pairHom Y α β) g :
          Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ) (Sum.inl v) (Sum.inl (β g v)) := by
  rw [coe_rotConjHom, coe_unitaryGroup_inv, coe_rotUnitary, coe_pairHom]
  exact colE_mul
    (colE_mul (colE_rotMatrix_conjTranspose_inr Y c s (β g v) hc' hs')
      (colE_blockDiag_inr Y (colE_pmat Y (β g) v)))
    (colE_rotMatrix_inl Y c s v hc hs)

end

end GroupApproximation.Full.NN01b
